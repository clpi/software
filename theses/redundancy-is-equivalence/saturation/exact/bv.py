"""Finest-grain semantics for the obligation language, in Z3.

Every variable ranges over all 2^64 two's-complement values, and every
index read idx_s(e) and call f(args) is an uninterpreted function: an
equality holds only if it holds for every input and every callee.
Operators match wsat's eval exactly (wrapping arithmetic, shift amount
taken mod 64, arithmetic right shift, Euclidean division and remainder
with x/0 = x%0 = 0), so a point where eval disagrees is a valid
counterexample here too.
"""

import z3

W = 64


def parse(s):
    toks = s.replace("(", " ( ").replace(")", " ) ").split()
    pos = 0

    def go():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t != "(":
            return t
        head = toks[pos]
        pos += 1
        kids = []
        while toks[pos] != ")":
            kids.append(go())
        pos += 1
        return (head, *kids)

    return go()


class Sem:
    def __init__(self):
        self.vars, self.funs = {}, {}

    def var(self, name):
        if name not in self.vars:
            self.vars[name] = z3.BitVec(name, W)
        return self.vars[name]

    def fun(self, name, arity):
        k = (name, arity)
        if k not in self.funs:
            self.funs[k] = z3.Function(f"{name}/{arity}", *([z3.BitVecSort(W)] * (arity + 1)))
        return self.funs[k]

    def term(self, t):
        if isinstance(t, str):
            if t.lstrip("-").isdigit():
                return z3.BitVecVal(int(t) & ((1 << W) - 1), W)
            return self.var(t)
        h, *k = t
        if h == "idx":
            return self.fun("idx_" + k[0], 1)(self.term(k[1]))
        if h == "call":
            args = [self.term(x) for x in k[1:]]
            if not args:
                return self.fun("call_" + k[0], 0)() if False else z3.BitVec("call_" + k[0], W)
            return self.fun("call_" + k[0], len(args))(*args)
        a = [self.term(x) for x in k]
        if h == "+":
            return a[0] + a[1]
        if h == "*":
            return a[0] * a[1]
        if h == "-":
            return a[0] - a[1]
        if h == "neg":
            return -a[0]
        if h == "<<":
            return a[0] << (a[1] & 63)
        if h == ">>":
            return a[0] >> (a[1] & 63)  # arithmetic, as i64::wrapping_shr
        if h in ("//", "%"):
            x, y = a
            r = z3.SRem(x, y)
            r = z3.If(r < 0, r + z3.If(y < 0, -y, y), r)
            if h == "%":
                return z3.If(y == 0, z3.BitVecVal(0, W), r)
            return z3.If(y == 0, z3.BitVecVal(0, W), (x - r) / y)
        if h == "&":
            return a[0] & a[1]
        if h == "|":
            return a[0] | a[1]
        if h == "^":
            return a[0] ^ a[1]
        raise ValueError(h)


def decide(a, b, timeout_ms=10000):
    """Return ('equal'|'differ'|'unknown', counterexample env or None)."""
    sem = Sem()
    ta, tb = sem.term(parse(a)), sem.term(parse(b))
    s = z3.Solver()
    s.set("timeout", timeout_ms)
    s.add(ta != tb)
    r = s.check()
    if r == z3.unsat:
        return "equal", None
    if r == z3.sat:
        m = s.model()
        env = {n: m.eval(v, model_completion=True).as_signed_long() for n, v in sem.vars.items()}
        return "differ", env
    return "unknown", None
