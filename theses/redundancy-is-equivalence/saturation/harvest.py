"""Harvest real equivalence obligations from Idol source in idol-lib.

For every definition, straight-line blocks (runs of `name = expr`) and
straight-line loop bodies are executed symbolically. A loop body is also
unrolled two and four times. Every pair (block or unrolled body) x
(block or unrolled body) inside one file, for every variable both
assign, gives one obligation: are the two final terms of that variable
equal? Most pairs are not; the witness rows refute those.

Only the arithmetic subset is read: identifiers, integers, + - * // %
& | ^ << >>, unary minus, indexing a[e] and calls f(e, ...). A line
outside it ends the block. Nothing here runs Idol.

Usage: python3 harvest.py IDOL_LIB OUT.tsv [--cross]

With --cross, units are also paired across files and across homes
(components), for every variable both assign: obligations that cross
component boundaries. Within-file pairs are left out in that mode.
"""

import os
import re
import sys

TOK = re.compile(r"\s*(?:(\d+)|([A-Za-z_][A-Za-z_0-9]*)|(//|<<|>>|[-+*%&|^()\[\],]))")


class Unsupported(Exception):
    pass


def lex(s):
    out, pos = [], 0
    s = s.rstrip()
    while pos < len(s):
        m = TOK.match(s, pos)
        if not m or m.end() == pos:
            raise Unsupported(s[pos:])
        pos = m.end()
        out.append(m.group(1) or m.group(2) or m.group(3))
    return out


PREC = {"|": 1, "^": 2, "&": 3, "<<": 4, ">>": 4, "+": 5, "-": 5, "*": 6, "//": 6, "%": 6}
HEAD = {"//": "//", "%": "%", "&": "&", "|": "|", "^": "^", "<<": "<<", ">>": ">>", "+": "+", "-": "-", "*": "*"}


class P:
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def take(self, x=None):
        tok = self.peek()
        if tok is None or (x is not None and tok != x):
            raise Unsupported(f"expected {x} got {tok}")
        self.i += 1
        return tok

    def expr(self, minp=0):
        left = self.unary()
        while True:
            op = self.peek()
            if op not in PREC or PREC[op] < minp:
                return left
            self.take()
            right = self.expr(PREC[op] + 1)
            left = (HEAD[op], left, right)

    def unary(self):
        if self.peek() == "-":
            self.take()
            return ("neg", self.unary())
        return self.postfix()

    def postfix(self):
        tok = self.take()
        if tok == "(":
            e = self.expr()
            self.take(")")
            node = e
        elif tok.isdigit():
            node = int(tok)
        elif re.match(r"[A-Za-z_]", tok):
            node = tok
        else:
            raise Unsupported(tok)
        while self.peek() in ("[", "("):
            if self.peek() == "[":
                if not isinstance(node, str):
                    raise Unsupported("index of non-name")
                self.take("[")
                e = self.expr()
                self.take("]")
                node = ("idx", node, e)
            else:
                if not isinstance(node, str):
                    raise Unsupported("call of non-name")
                self.take("(")
                args = []
                if self.peek() != ")":
                    args.append(self.expr())
                    while self.peek() == ",":
                        self.take(",")
                        args.append(self.expr())
                self.take(")")
                node = ("call", node, *args)
        return node


def parse_expr(s):
    p = P(lex(s))
    e = p.expr()
    if p.peek() is not None:
        raise Unsupported("trailing")
    return e


KEYWORDS = {"while", "if", "else", "elif", "for", "return", "break", "continue", "true", "false", "and", "or", "not"}


def subst(e, env):
    if isinstance(e, int):
        return e
    if isinstance(e, str):
        return env.get(e, e)
    if e[0] == "idx":
        return ("idx", e[1], subst(e[2], env))
    if e[0] == "call":
        return ("call", e[1], *[subst(a, env) for a in e[2:]])
    return (e[0], *[subst(a, env) for a in e[1:]])


def sexpr(e):
    if isinstance(e, int):
        return str(e)
    if isinstance(e, str):
        return e
    if e[0] == "idx":
        return f"(idx {e[1]} {sexpr(e[2])})"
    if e[0] == "call":
        return "(call " + e[1] + "".join(" " + sexpr(a) for a in e[2:]) + ")"
    return "(" + e[0] + "".join(" " + sexpr(a) for a in e[1:]) + ")"


def tsize(e):
    if isinstance(e, (int, str)):
        return 1
    return 1 + sum(tsize(a) for a in e[1:] if not (e[0] in ("idx", "call") and a is e[1]))


ASSIGN = re.compile(r"^([A-Za-z_][A-Za-z_0-9]*)\s*=\s*(.+)$")


def statements(lines):
    """Yield (indent, kind, payload) with kind in assign|while|other."""
    for raw in lines:
        if not raw.strip() or raw.strip().startswith("#"):
            continue
        ind = len(raw) - len(raw.lstrip(" "))
        s = raw.strip()
        m = ASSIGN.match(s)
        if m and m.group(1) not in KEYWORDS and "==" not in s:
            try:
                yield ind, "assign", (m.group(1), parse_expr(m.group(2)))
                continue
            except Unsupported:
                yield ind, "other", s
                continue
        if s.startswith("while "):
            yield ind, "while", s
        else:
            yield ind, "other", s


def blocks_of(def_lines):
    """Straight-line blocks and loop bodies of one definition."""
    st = list(statements(def_lines))
    blocks, loops = [], []
    cur, cur_ind = [], None
    for idx, (ind, kind, pay) in enumerate(st):
        if kind == "assign" and (cur_ind is None or ind == cur_ind):
            cur.append(pay)
            cur_ind = ind
        else:
            if len(cur) >= 2:
                blocks.append(cur)
            cur, cur_ind = ([pay], ind) if kind == "assign" else ([], None)
        if kind == "while":
            body, j = [], idx + 1
            body_ind = None
            ok = True
            while j < len(st) and st[j][0] > ind:
                if st[j][1] != "assign" or (body_ind is not None and st[j][0] != body_ind):
                    ok = False
                    break
                body_ind = st[j][0]
                body.append(st[j][2])
                j += 1
            if ok and body:
                loops.append(body)
    if len(cur) >= 2:
        blocks.append(cur)
    return blocks, loops


def run_block(stmts, times=1):
    env = {}
    for _ in range(times):
        for name, e in stmts:
            env[name] = subst(e, env)
    return env


def defs_of(text):
    lines = text.split("\n")
    out, cur, name = [], [], None
    for ln in lines:
        m = re.match(r"^([A-Za-z_][A-Za-z_0-9]*)\s*=\s*\(", ln)
        if m and not ln.startswith(" "):
            if name:
                out.append((name, cur))
            name, cur = m.group(1), []
        elif name and (ln.startswith(" ") or not ln.strip()):
            cur.append(ln)
        elif name:
            out.append((name, cur))
            name, cur = None, []
    if name:
        out.append((name, cur))
    return out


def main(root, out_path, cross=False):
    obligations = []
    files = 0
    allunits = []
    for home in sorted(os.listdir(root)):
        d = os.path.join(root, home)
        if not os.path.isdir(d) or home in ("graphs", "space", "kernel", "tools", "port", "redundant"):
            continue
        for fn in sorted(os.listdir(d)):
            if not fn.endswith(".id"):
                continue
            files += 1
            text = open(os.path.join(d, fn), encoding="utf-8", errors="replace").read()
            units = []
            for dname, lines in defs_of(text):
                blocks, loops = blocks_of(lines)
                for bi, b in enumerate(blocks):
                    units.append((f"{dname}.b{bi}", run_block(b)))
                for li, l in enumerate(loops):
                    for k in (1, 2, 4):
                        units.append((f"{dname}.l{li}x{k}", run_block(l, k)))
            allunits.extend((home, fn, na, ea) for na, ea in units)
            if cross:
                continue
            seen = set()
            for i in range(len(units)):
                for j in range(i + 1, len(units)):
                    (na, ea), (nb, eb) = units[i], units[j]
                    for v in sorted(set(ea) & set(eb)):
                        a, b = ea[v], eb[v]
                        if a == b or tsize(a) > 120 or tsize(b) > 120:
                            continue
                        key = (sexpr(a), sexpr(b))
                        if key in seen:
                            continue
                        seen.add(key)
                        oid = f"{home}/{fn}:{na}~{nb}:{v}"
                        obligations.append((oid, f"real:{home}", sexpr(a), sexpr(b)))
    if cross:
        seen = set()
        byvar = {}
        for u in allunits:
            for v in u[3]:
                byvar.setdefault(v, []).append(u)
        for v in sorted(byvar):
            us = byvar[v]
            for i in range(len(us)):
                for j in range(i + 1, len(us)):
                    (ha, fa, na, ea), (hb, fb, nb, eb) = us[i], us[j]
                    if (ha, fa) == (hb, fb):
                        continue
                    a, b = ea[v], eb[v]
                    if a == b or tsize(a) > 120 or tsize(b) > 120:
                        continue
                    key = (sexpr(a), sexpr(b))
                    if key in seen or (key[1], key[0]) in seen:
                        continue
                    seen.add(key)
                    kind = "cross-file" if ha == hb else "cross-home"
                    obligations.append((f"{ha}/{fa}:{na}~{hb}/{fb}:{nb}:{v}", f"{kind}:{ha}+{hb}", sexpr(a), sexpr(b)))
    with open(out_path, "w") as f:
        for o in obligations:
            f.write("\t".join(o) + "\n")
    print(f"files {files}, obligations {len(obligations)}", file=sys.stderr)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], "--cross" in sys.argv[3:])
