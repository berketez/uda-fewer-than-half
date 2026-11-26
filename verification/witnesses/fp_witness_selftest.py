"""Consistency test of rank_modp_parcali against rank_det_modp (and against the known rank); extra: lower-bound check of the DP.
Run from the package root (the DP module is imported from thresholds/)."""
import numpy as np, sys
sys.path.insert(0, "thresholds")
from fp_witness import rank_det_modp, rank_modp_parcali
import dp_glue as u8_dp
p = 1000037
rng = np.random.default_rng(5)
for (m, k, r) in [(300, 320, 300), (300, 320, 257), (500, 450, 450), (512, 600, 511), (64, 64, 17)]:
    L = rng.integers(0, p, size=(m, r)); R = rng.integers(0, p, size=(r, k))
    A = np.zeros((m, k), dtype=np.int64)
    for j0 in range(0, r, 64):                  # exact: chunk by chunk, mod p
        A = (A + (L[:, j0:j0+64] @ R[j0:j0+64] % p)) % p   # |intermediate| < 64 p^2 < 2^63
    r1, _ = rank_det_modp(A, p); r2 = rank_modp_parcali(A.copy(), p, parca=37)
    print(f"m={m} k={k} planted rank {r}: rank_det_modp = {r1}, rank_modp_parcali = {r2}  {'✓' if r1 == r2 == r else '✗'}")
P, cg = u8_dp.calistir("V2", set(range(2, 14)))
K = {n: min(max(a, b) for a, b, c in P[n]) for n in P}
print("DP lower-bound check: min_n (K_V2 − K_count) =", min(K[n] - u8_dp.K_say(n) for n in K), "(must not be negative)")
