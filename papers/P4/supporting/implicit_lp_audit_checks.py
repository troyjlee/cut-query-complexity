#!/usr/bin/env python3
"""Exact checks for examples in implicit-lp-audit.tex, not an LP solver test."""
from fractions import Fraction as F


def mv(a, x):
    return tuple(sum(v * w for v, w in zip(row, x)) for row in a)


def transpose(a):
    return tuple(zip(*a))


def normal(a, d):
    at = transpose(a)
    return tuple(tuple(sum(d[k] * x[k] * y[k] for k in range(len(d)))
                       for y in at) for x in at)


def rhs(a, d, q):
    return mv(transpose(a), tuple(di * qi for di, qi in zip(d, q)))


def solve2(a, b):
    det = a[0][0] * a[1][1] - a[0][1] * a[1][0]
    assert det != 0
    return ((a[1][1] * b[0] - a[0][1] * b[1]) / det,
            (a[0][0] * b[1] - a[1][0] * b[0]) / det)


def energy2(a, x):
    return sum(u * v for u, v in zip(x, mv(a, x)))


def mul(p, q):
    result = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            result[i + j] += a * b
    return result


def main():
    a = ((F(1), F(-1)), (F(1), F(0)), (F(0), F(1)))
    d = (F(1),) * 3
    q = (F(1), F(-1), F(1))
    l = normal(a, d)
    assert rhs(a, d, q) == (0, 0)
    for bits in range(1, 81):
        eta = F(1, 2 ** bits)
        dhat = (1 + eta, F(1), F(1))
        lhat = normal(a, dhat)
        bhat = rhs(a, dhat, q)
        phat = solve2(lhat, bhat)
        expected = eta / (3 + 2 * eta)
        assert phat == (expected, -expected)
        assert energy2(l, phat) > 0  # Relative error to the true zero is impossible.

        tau = eta ** 2
        qsmall = (1 + tau, F(-1), F(1))
        p = solve2(l, rhs(a, d, qsmall))
        phat = solve2(lhat, rhs(a, dhat, qsmall))
        error = tuple(x - y for x, y in zip(phat, p))
        ratio = eta * (3 + tau) / (tau * (3 + 2 * eta))
        assert energy2(l, error) == ratio ** 2 * energy2(l, p)
        assert ratio > 1

    # Repair on the two explicit +I rows, for independent raw directions.
    for i in range(-5, 6):
        for j in range(-5, 6):
            raw = (F(i, 3), F(j, 7), F(i - j, 11))
            residual = mv(transpose(a), raw)
            repaired = (raw[0], raw[1] - residual[0], raw[2] - residual[1])
            assert mv(transpose(a), repaired) == (0, 0)

    # Exact polynomial identity in z=1/k for the centrality proxy proof.
    product = mul(mul([F(1), F(1, 2)], [F(1), F(-6, 7)]),
                  [F(1), F(1, 16)])
    assert product == [F(1), F(-33, 112), F(-101, 224), F(-3, 112)]
    assert F(33, 112) - F(1, 40) == F(151, 560) > F(1, 4)

    def support(tau):
        return min(tau, 1 - tau)

    assert support(F(1, 3)) == support(F(2, 3)) == F(1, 3)
    assert support(F(1, 2)) - support(F(1, 3)) == F(1, 6)
    print("PASS: 80 cancellation and 80 nonzero-RHS examples; 121 exact repairs;")
    print("      centrality polynomial identity; support-search counterexample.")


if __name__ == '__main__':
    main()
