"""Mechanism suites: one per divergence mechanism and search component
named in the design, written to exercise it. These are targeted tests,
not samples of real code; the real-code suite is harvest.py's output.

Usage: python3 suites.py OUT.tsv
"""

import sys


def s(*xs):
    return "(" + " ".join(xs) + ")"


def chain(op, xs):
    acc = xs[0]
    for x in xs[1:]:
        acc = s(op, acc, x)
    return acc


def rchain(op, xs):
    acc = xs[-1]
    for x in reversed(xs[:-1]):
        acc = s(op, x, acc)
    return acc


def main(out):
    rows = []
    # AC blowup: n operands, reversed and rebracketed
    for n in (6, 10, 14, 20):
        v = [f"x{i}" for i in range(n)]
        rows.append((f"ac{n}+", "ac", chain("+", v), rchain("+", list(reversed(v)))))
        rows.append((f"ac{n}*", "ac", chain("*", v), rchain("*", v[1::2] + v[0::2])))
    # e-matching join explosion: factor over fat classes
    for k in (3, 5, 7, 9):
        bs = [f"b{i}" for i in range(k)]
        rows.append((f"join{k}", "join", chain("+", [s("*", "a", b) for b in bs]), s("*", "a", chain("+", bs))))
        rows.append((f"join{k}c", "join", chain("+", [s("*", b, "a") for b in bs]), s("*", chain("+", bs), "a")))
    # generative rules: run with --gen; plain targets, the rule only churns
    for i, (a, b) in enumerate([("(+ (* a b) c)", "(+ c (* b a))"), ("(* (+ x y) z)", "(* z (+ y x))"),
                                ("(+ x (+ y z))", "(+ (+ x y) z)"), ("(<< x 3)", "(* 8 x)")]):
        rows.append((f"gen{i}", "gen", a, b))
    # cycles: merges that put a class inside itself (x = x*1, x = x+0)
    for i, (a, b) in enumerate([("(* x 1)", "x"), ("(+ (* (+ x 0) 1) y)", "(+ y x)"),
                                ("(* (* (* x 1) 1) (+ y 0))", "(* y x)"), ("(+ (+ x 0) (* (+ y 0) 1))", "(+ y x)")]):
        rows.append((f"cycle{i}", "cycle", a, b))
    # valleys: the proof must pass through a larger term (distribute first)
    for i, (a, b) in enumerate([
        ("(- (* a (+ b c)) (* a b))", "(* a c)"),
        ("(- (* (+ b c) a) (* c a))", "(* b a)"),
        ("(- (* a (+ b (+ c d))) (* a (+ b c)))", "(* a d)"),
        ("(+ (* a (- b c)) (* a c))", "(* a b)"),
        ("(- (* x (+ y 1)) x)", "(* x y)"),
        ("(- (* (+ p q) (+ r 1)) (+ p q))", "(* (+ p q) r)"),
    ]):
        rows.append((f"valley{i}", "valley", a, b))
    # meet in the middle: both sides need work toward a shared middle
    for k in (1, 2, 3):
        terms_a = [s("*", "a", s("+", f"b{j}", f"c{j}")) for j in range(k)]
        terms_b = [s("+", s("*", "a", f"b{j}"), s("*", "a", f"c{j}")) for j in range(k)]
        rows.append((f"mid{k}", "mid", chain("+", terms_a + ["d"]), chain("+", ["d"] + list(reversed(terms_b)))))
    # refuted near-misses: structure close, behavior differs on few points
    for i, (a, b) in enumerate([("(+ (* a b) 1)", "(+ (* a b) (// a a))"), ("(* x 2)", "(<< x 2)"),
                                ("(- x y)", "(- y x)"), ("(* (+ a b) (+ a b))", "(+ (* a a) (* b b))"),
                                ("(+ (* 4 a) (* 3 b))", "(+ (* 3 a) (* 4 b))")]):
        rows.append((f"near{i}", "refuted", a, b))
    # rare differences: equal on almost every input, different on a
    # sliver no sample of 64 points is likely to hit. Equality here is
    # false at the finest grain, so any engine that joins one is wrong.
    for i, (a, b) in enumerate([
        ("(+ y (// 1 (+ (^ x 1234567) 1)))", "y"),
        ("(* x (// 1 (+ (& x 1099511627775) 1)))", "0"),
        ("(- (* a b) (* 7 (// 1 (+ (^ (^ a b) -7046029254386353131) 1))))", "(* a b)"),
    ]):
        rows.append((f"rare{i}", "rare", a, b))
    with open(out, "w") as f:
        for r in rows:
            f.write("\t".join(r) + "\n")


if __name__ == "__main__":
    main(sys.argv[1])
