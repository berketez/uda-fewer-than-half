"""Smallest value of the margin of K-1 < 2kc n + 4log2 n for the logarithmic choice (n in [274,5000]) and the tail bounds.
Tail (n >= 4740): K <= 2kc n + (4-2kc)log2 n + 5 - 2kc <= 2kc n + 4 log2 n  <=>  2kc log2 n >= 5 - 2kc."""
import math
from decimal import Decimal, getcontext
getcontext().prec = 60
kc_lo = Decimal("0.1892896249"); LN2 = Decimal(2).ln()
enk = None
for n in range(274, 5001):
    t = (n - 1).bit_length(); m = n - t
    L = math.ceil(0.1892896249 * m + math.log2(m))
    K = 2 * (L + t) + 1
    marj = 2 * kc_lo * n + 4 * Decimal(n).ln() / LN2 - (K - 1)
    if enk is None or marj < enk[0]:
        enk = (marj, n, K)
print("smallest margin (rhs - (K-1)) for n in [274,5000]:", float(enk[0]), "n =", enk[1], "K =", enk[2])
kc = 0.1892896249
print("tail threshold: log2 n >= (5-2kc)/(2kc) =", (5 - 2 * kc) / (2 * kc), "=> n >=", math.ceil(2 ** ((5 - 2 * kc) / (2 * kc))))
# tail of B >= 2^(m+2): m needed for x=L/m <= kc+(log2 m+1)/m <= 0.2
m = 100
while kc + (math.log2(m) + 1) / m > 0.2:
    m += 1
print("for x <= 0.2: m >=", m, "; f'(0.2)=log2 12 =", math.log2(12))
