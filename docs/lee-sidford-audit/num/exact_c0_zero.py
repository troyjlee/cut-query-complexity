# Exact counterexample to LS (arXiv 1910.08033v2) Lemma 26 / Theorem 29 with c0 = 0.
# p = 1/2, one column: one entry 1 and K = 8000 entries 1/400.  Exact rational arithmetic.
# Lewis weights w_i = sigma(W^{1/2-1/p} A)_i, i.e. w_i = w_i^{1-2/p} a_i^2 / H with
# H = sum_j w_j^{1-2/p} a_j^2.  For p = 1/2: w_i^4 = a_i^2 / H, so w_i is proportional to sqrt|a_i|.
from fractions import Fraction as F
K = 8000
a0, a1 = F(1), F(1, 400)
w0, w1 = F(1, 401), F(1, 8020)          # proportional to sqrt(a): 1 : 1/20, summing to 1 = n
assert w0 + K * w1 == 1
H = w0**-3 * a0**2 + K * w1**-3 * a1**2  # A^T W^{1-2/p} A
assert w0 == w0**-3 * a0**2 / H and w1 == w1**-3 * a1**2 / H   # exact Lewis fixed point
G = a0**2 / w0 + K * a1**2 / w1          # A^T W^{-1} A  (c0 = 0, g = w)
cs0 = a0**2 / G / w0**2                  # sensitivity of row 0
m = K + 1
print('c_s(row 0) =', cs0, '=', float(cs0))
assert cs0 == F(401, 2)
assert cs0**2 > 4 * m                    # 401/2 > 2 sqrt(8001) = LS bound 2 m^{1-p}
print('LS bound 2 m^(1-p) = 2 sqrt(8001) =', 2 * m**0.5)
