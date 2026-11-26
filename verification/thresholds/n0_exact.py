"""Re-verification of the N0 thresholds of Theorem 1 in INTEGER arithmetic only.

(*)  2^t log2(B_m(L)/2^m) > 2m   <=>   B_m(L)^(2^t) > 2^(m*2^t + 2m)   (integer comparison)

Modes:
  a LO HI   : n in [LO,HI], the optimised (t,L) search rule (floating point only as a hint);
              (*) checked in integers for the chosen (t,L); K=2(L+t)+1 < n/2 and K <= ceil(0.4n) checked in integers.
              Lists the n that do not satisfy K < n/2.
  b MLO MHI : choice t=7, L=floor(0.195 m) (exact: 195*m//1000); m in [MLO,MHI]; (*) in integers.
  c LO HI   : logarithmic choice t=ceil(log2 n), m=n-t, L=ceil(kc*m+log2 m) (hint); sufficient condition
              B_m(L) >= 2^(m+2) (implies (*) because 2^t >= n > m) in integers; and
              K=2(L+t)+1 <= 2*kc_lo*n + 4*log2 n (Decimal, 60 digits, kc_lo = 0.1892896249 < kappa_c, checked).
Run: OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 nice -n 15 python3 -u n0_exact.py a 100 1660
"""
import math
import sys
from decimal import Decimal, getcontext

getcontext().prec = 60
LOG2_3 = math.log2(3)


def B_exact(m, L):
    s, term = 0, 1
    for j in range(0, L + 1):
        if j > 0:
            term = term * (m - j + 1) * 3 // j
        s += term
    return s


def star_exact(m, L, t):
    B = B_exact(m, L)
    return pow(B, 2 ** t) > (1 << (m * 2 ** t + 2 * m))


def log2B_float(m, L):
    lg = math.lgamma
    j0 = max(0, L - 80)
    terms = [(lg(m + 1) - lg(j + 1) - lg(m - j + 1)) / math.log(2) + j * LOG2_3 for j in range(j0, L + 1)]
    mx = max(terms)
    return mx + math.log2(sum(2.0 ** (x - mx) for x in terms))


def Lstar_float(m, t, kc=0.1892896249):
    ok = lambda L: (2 ** t) * (log2B_float(m, L) - m) > 2 * m
    lo, hi = max(0, int(kc * m) - 3), m
    if not ok(hi):
        return None
    if ok(lo):
        return lo
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if ok(mid):
            hi = mid
        else:
            lo = mid
    return hi


def kip_a(lo, hi):
    yari_kotu, p4_kotu, tasma = [], [], []
    for n in range(lo, hi + 1):
        best = None
        for t in range(1, min(24, int(math.log2(n)) + 6)):
            L = Lstar_float(n - t, t)
            if L is None:
                continue
            K = 2 * (L + t) + 1
            if best is None or K < best[0]:
                best = (K, t, L)
        K, t, L = best
        m = n - t
        while not star_exact(m, L, t):
            L += 1
            tasma.append(n)
        K = 2 * (L + t) + 1
        if not (2 * K < n):
            yari_kotu.append(n)
        if not (K <= -((-4 * n) // 10)):
            p4_kotu.append(n)
    print(f"[a] n in [{lo},{hi}] (integer (*))")
    print(f"    n with K >= n/2 (>=120): {[x for x in yari_kotu if x >= 120]}; total {len(yari_kotu)}")
    print(f"    n with K > ceil(0.4n) (>=980): {[x for x in p4_kotu if x >= 980]}; total {len(p4_kotu)}")
    print(f"    number of n where the floating-point hint had to be corrected in integers: {len(tasma)}")


def kip_b(mlo, mhi):
    kotu = []
    for m in range(mlo, mhi + 1):
        L = (195 * m) // 1000
        if not star_exact(m, L, 7):
            kotu.append(m)
        n = m + 7
        K = 2 * (L + 7) + 1
        assert 2 * K < n, (m, K)
        assert K <= -((-4 * n) // 10), (m, K)
    print(f"[b] t=7, L=floor(0.195m), m in [{mlo},{mhi}]: number of m where (*) fails in integers: {len(kotu)} {kotu[:10]}")


def kip_c(lo, hi):
    kc = Decimal("0.18928962494")  # hint; below, f(kc_lo) < 1 is checked exactly
    # kc_lo: a lower bound with f(kc_lo) < 1 (f is increasing on [0,3/4]) -> 2*kc_lo*n is a lower bound
    def f_dec(x):
        x = Decimal(x)
        return (-(x * x.ln()) - (1 - x) * (1 - x).ln()) / Decimal(2).ln() + x * (Decimal(3).ln() / Decimal(2).ln())
    kc_lo = Decimal("0.1892896249")
    assert f_dec(kc_lo) < 1, "kc_lo is not a lower bound"
    LN2 = Decimal(2).ln()
    kotu_B, kotu_K = [], []
    for n in range(lo, hi + 1):
        t = (n - 1).bit_length()  # ceil(log2 n)
        m = n - t
        L = math.ceil(0.1892896249 * m + math.log2(m))
        B = B_exact(m, L)
        if not (B >= (1 << (m + 2))):
            kotu_B.append(n)
        K = 2 * (L + t) + 1
        sag = 2 * kc_lo * n + 4 * Decimal(n).ln() / LN2
        # claim K(n) = ceil(2kc n + 4 log2 n); for an integer K, K <= ceil(x) <=> K - 1 < x
        if not (Decimal(K - 1) < sag):
            kotu_K.append(n)
    print(f"[c] log choice, n in [{lo},{hi}]: B>=2^(m+2) fails: {kotu_B[:10]} (total {len(kotu_B)}); "
          f"K <= ceil(2kc n + 4log2 n) fails: first {kotu_K[:10]}, last {kotu_K[-5:]} (total {len(kotu_K)})")


if __name__ == "__main__":
    kip = sys.argv[1]
    a, b = int(sys.argv[2]), int(sys.argv[3])
    {"a": kip_a, "b": kip_b, "c": kip_c}[kip](a, b)
