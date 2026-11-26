"""Exact integer confirmation of the example values of the optimised construction quoted in the paper
(Sec. "Proof of Theorem 1", explicit thresholds): K = 93 at n = 200, K = 399 at n = 1000, K = 1161 at n = 3000.

NEW in this package (no original script). It reuses, unchanged, the functions of n0_exact.py:
  * the choice of (t, L) is the search rule of mode `a` of n0_exact.py: for every t in 1 .. min(23, floor(log2 n) + 5)
    the floating-point hint Lstar_float(n - t, t) gives the smallest L for which (*) appears to hold, and the t with the
    smallest K = 2(L + t) + 1 is kept (the first such t if several give the same K);
  * for the chosen (t, L) condition (*), i.e. B_m(L)^(2^t) > 2^(m 2^t + 2m) with m = n - t, is then evaluated in exact
    integer arithmetic (star_exact), once for L and once for L - 1.
What this proves: (*) holds for the chosen (t, L), so K(n) = 2(L + t) + 1 is a valid value of the construction; and
(*) fails for L - 1 at the same t. Since B_m(L) increases with L, L is then the smallest valid L for the chosen t.
What it does not prove: that no other t gives a smaller K. The comparison between different t uses the
floating-point hint only.
Usage: python3 thresholds/examples_exact.py
"""
import math
import sys

from n0_exact import Lstar_float, star_exact

PAPER = {200: 93, 1000: 399, 3000: 1161}

ok_all = True
for n, k_paper in PAPER.items():
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
    at_L = star_exact(m, L, t)
    at_L1 = star_exact(m, L - 1, t)
    ok = at_L and not at_L1 and K == k_paper
    ok_all &= ok
    print(f"n = {n}: chosen t = {t}, L = {L}, m = {m}; K = 2(L+t)+1 = {K} (paper: {k_paper}); "
          f"(*) in integers with L: {at_L}; with L-1: {at_L1}; K/n = {K / n:.4f}", flush=True)
print("RESULT:", "all three example values confirmed in integers for the chosen t (smallest L for that t)"
      if ok_all else "AT LEAST ONE EXAMPLE VALUE NOT CONFIRMED")
sys.exit(0 if ok_all else 1)
