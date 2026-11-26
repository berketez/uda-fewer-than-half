"""Constants of Lemma 3 / Theorem 1 and the explicit N0 computation.

Condition (*): 2^t * log2(B_m(L) / 2^m) > 2m,  B_m(L) = sum_{j<=L} C(m,j) 3^j.
Choice for the 0.4n row: t = 7, m = n - 7, L = floor(0.195 m), K = 2(L+t)+1.
Choice for the logarithmic row: t = ceil(log2 n), m = n - t, L = ceil(kappa_c m + log2 m), K = 2(L+t)+1.

Exactness: condition (*) is also tested in integers:  B^(2^t) > 2^(m 2^t + 2m)
  <=>  2^t * (log2 B - m) > 2m. Instead of computing this from the leading bits of log2 B, the integer comparison
  is done directly (B^128 for t = 7; fast for m <= ~3000).
For large m a floating-point log-sum is used together with an explicit analytic tail bound.
Note: the scans below that use floating point (log2B_float) only locate thresholds; the explicit thresholds of
the paper rest on the exact integer checks of n0_exact.py and on the analytic tail bounds.
"""
import math
import sys
from functools import lru_cache

LOG2_3 = math.log2(3.0)


def h2(x):
    if x <= 0 or x >= 1:
        return 0.0
    return -x * math.log2(x) - (1 - x) * math.log2(1 - x)


def f(x):
    return h2(x) + x * LOG2_3


def fp(x):  # f'(x) = log2(3 (1-x)/x)
    return math.log2(3 * (1 - x) / x)


def kappa_c():
    lo, hi = 0.01, 0.5
    for _ in range(200):
        mid = (lo + hi) / 2
        if f(mid) < 1:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def B_exact(m, L):
    s = 0
    term = 1
    for j in range(0, L + 1):
        if j > 0:
            term = term * (m - j + 1) * 3 // j
        s += term
    return s


def log2B_float(m, L):
    # log-sum-exp with lgamma
    lg = math.lgamma
    # only the last 80 terms: the ratio of consecutive terms is L/(3(m-L+1)) <= ~0.1 (L <= 0.25 m), truncation error < 0.1^80
    j0 = max(0, L - 80)
    terms = [(lg(m + 1) - lg(j + 1) - lg(m - j + 1)) / math.log(2) + j * LOG2_3 for j in range(j0, L + 1)]
    mx = max(terms)
    return mx + math.log2(sum(2.0 ** (x - mx) for x in terms))


def cond_exact(m, L, t):
    """Integer test of condition (*): B^(2^t) > 2^(m 2^t + 2m)."""
    B = B_exact(m, L)
    T = 2 ** t
    # quick pre-screening with bit lengths
    lhs_bits_hi = T * B.bit_length()          # log2(B^T) < T*bitlen
    lhs_bits_lo = T * (B.bit_length() - 1)    # log2(B^T) >= T*(bitlen-1)
    rhs = m * T + 2 * m
    if lhs_bits_lo > rhs:
        return True
    if lhs_bits_hi <= rhs:
        return False
    return B ** T > (1 << rhs)


def main():
    kc = kappa_c()
    beta = 0.195
    print(f"kappa_c = {kc:.10f}, 2 kappa_c = {2*kc:.10f}, f'(kappa_c) = {fp(kc):.6f}")
    print(f"f(0.195) - 1 = {f(beta)-1:.10f}; 2^7 (f(0.195)-1) = {128*(f(beta)-1):.7f}")
    print(f"f'(0.195) = {fp(beta):.6f}")

    # --- choice c = 0.4: from which m on does (*) hold? (floating-point scan, then integer confirmation)
    t = 7
    Mmax = 60000
    last_fail = None
    for m in range(1, Mmax + 1):
        L = math.floor(beta * m)
        g = (2 ** t) * (log2B_float(m, L) - m) - 2 * m
        if g <= 0:
            last_fail = m
    print(f"[t=7, L=floor(0.195 m)] floating point: last m where (*) fails = {last_fail} (scan m <= {Mmax})")
    # integer confirmation around the threshold
    lo = max(1, last_fail - 300)
    hi = last_fail + 1500
    ex_last_fail = None
    for m in range(lo, hi + 1):
        L = math.floor(beta * m)
        if not cond_exact(m, L, t):
            ex_last_fail = m
    print(f"  integer confirmation m in [{lo},{hi}]: last failing m = {ex_last_fail}")
    # margin beyond the threshold
    for m in [ex_last_fail, ex_last_fail + 1, ex_last_fail + 10, ex_last_fail + 100, 5000, 20000, 60000]:
        L = math.floor(beta * m)
        g = (2 ** t) * (log2B_float(m, L) - m) - 2 * m
        print(f"  m={m}: L={L}, 2^7 log2(B/2^m) - 2m = {g:.3f}")

    # analytic tail: C(m,L) >= 2^{m h(L/m)} / sqrt(8 L (1-L/m)), L/m >= beta - 1/m, f increasing and concave
    # g(m) >= 128 [ m (f(beta)-1) - f'(beta - 1/M) - 0.5 log2(8 beta (1-beta) m) ] - 2m  (m >= M)
    M = 5000
    def g_low(m):
        return 128 * (m * (f(beta) - 1) - fp(beta - 1.0 / M) - 0.5 * math.log2(8 * beta * (1 - beta) * m)) - 2 * m
    print(f"  analytic lower bound g_low(M={M}) = {g_low(M):.2f}; derivative of g_low ~ 128(f-1) - 2 - 128/(2 m ln2) = "
          f"{128*(f(beta)-1) - 2 - 64/(M*math.log(2)):.4f} > 0 (m >= M)")

    # n side: K(n) = 2 floor(0.195 (n-7)) + 15 <= ceil(0.4 n) ?
    m0 = ex_last_fail + 1
    last_bad_n = None
    for n in range(8, 200000):
        m = n - 7
        K = 2 * math.floor(beta * m) + 15
        ok_cond = m >= m0
        ok_K = K <= math.ceil(0.4 * n)
        if not (ok_cond and ok_K):
            last_bad_n = n
    print(f"[c=0.4 choice] N0 = {last_bad_n + 1}  (for all n >= N0: (*) and K(n) <= ceil(0.4 n); scan n < 200000, "
          f"beyond: K <= 0.39 n + 12.27 <= 0.4 n, n >= 1227)")

    # --- logarithmic choice
    def U9log(n):
        tt = math.ceil(math.log2(n))
        m = n - tt
        L = math.ceil(kc * m + math.log2(m))
        return tt, m, L, 2 * (L + tt) + 1
    bad_cond, bad_K = None, None
    for n in range(16, 200001):
        tt, m, L, K = U9log(n)
        if L > m:
            bad_cond = n
            continue
        g = (2 ** tt) * (log2B_float(m, L) - m) - 2 * m
        if g <= 0:
            bad_cond = n
        if K > math.ceil(2 * kc * n + 4 * math.log2(n)):
            bad_K = n
    print(f"[log choice] last n where (*) fails = {bad_cond}; last n with K > ceil(2 kc n + 4 log2 n) = {bad_K} (scan n <= 200000)")
    for n in [100, 1000, 10000, 100000]:
        tt, m, L, K = U9log(n)
        print(f"  n={n}: t={tt}, L={L}, K={K}, 2kc n + 4log2 n = {2*kc*n+4*math.log2(n):.2f}, K/n = {K/n:.4f}")

    # --- optimised construction (same Lemma 3 framework): for each n, min_t 2(L*(n-t,t)+t)+1
    def ok(m, L, tt):
        return (2 ** tt) * (log2B_float(m, L) - m) > 2 * m

    def Lstar(m, tt):
        lo = max(0, int(kc * m) - 3)
        hi = m
        if not ok(m, hi, tt):
            return None
        if ok(m, lo, tt):
            return lo
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if ok(m, mid, tt):
                hi = mid
            else:
                lo = mid
        return hi

    def Kopt(n):
        best = None
        for tt in range(1, min(24, int(math.log2(n)) + 6)):
            m = n - tt
            if m < 2:
                break
            L = Lstar(m, tt)
            if L is None:
                continue
            K = 2 * (L + tt) + 1
            if best is None or K < best[0]:
                best = (K, tt, L)
        return best

    first_half = None
    last_bad04 = None
    rows = []
    cache = {}
    for n in range(10, 3001):
        cache[n] = Kopt(n)
        K, tt, L = cache[n]
        if K < n / 2 and first_half is None:
            first_half = (n, K, tt, L)
        if K > math.ceil(0.4 * n):
            last_bad04 = n
        if n in (50, 100, 200, 500, 1000, 2000, 3000):
            rows.append((n, K, tt, L, K / n))
    print(f"[optimised Lemma 3] first n with K < n/2: {first_half}")
    print(f"[optimised Lemma 3] last n with K > ceil(0.4 n) (n <= 3000): {last_bad04}")
    # does K < n/2 always hold after first_half?
    viol = [n for n in range(first_half[0], 3001) if cache[n][0] >= n / 2]
    print(f"  number of n after first_half with K >= n/2: {len(viol)}; examples {viol[:10]}")
    for r in rows:
        print(f"  n={r[0]}: K={r[1]} (t={r[2]}, L={r[3]}), K/n={r[4]:.4f}")
    # integer confirmation: the first point with K < n/2
    n, K, tt, L = first_half
    print(f"  integer confirmation (n={n}, t={tt}, L={L}): (*) = {cond_exact(n - tt, L, tt)}; with L-1 = {cond_exact(n - tt, L - 1, tt)}")


if __name__ == "__main__":
    main()
