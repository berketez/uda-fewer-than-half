"""Exact verifier for R(j) certificates: real spanning level j < K (the j-level form of D3-D4 of the S verifier).

R(j) at psi_0  <=>  span_R{P psi_0 : 0 <= |P| <= j} + R i psi_0 = C^D.  (An S certificate gives R(K) at the
locality K of H.)
  (V1), (V2): as in verify_C1.py (theta > s, A > 0 => lambda_1 > s > lambda_2).
  (V3R) G = B B^T >= tau' I; B (2D x (M_j + 2)) has as columns the embedded P w (0 <= |P| <= j) and i w.
  (V4R) 2(M_j + 2) r^2/(theta - s)^2 < tau'/w^dag w  => sigma_2D(B_psi0) > 0 => R(j) at psi_0.
The R certificate (parameters t, f) is looked up as certificates/R/R_n{n}_K{K}_j{j}_t{seed}.json, relative to
the CURRENT WORKING DIRECTORY (run from the package root), and is bound to the S certificate by SHA-256.
Parameter generation (--uret, not used in the package): t = floor(lambda_min/2) (floating point, a hint only),
f the largest safe value.
Usage: python3 verify_R.py <S certificate> <j> [--uret]
"""
import sys, json, hashlib, itertools, time
from fractions import Fraction
from math import comb
import numpy as np
sys.path.insert(0, "verifiers")
from verify_C1 import dur, maske, i_kuvvet, psd_kesin, pauli_listesi, SINIR

KOK = "certificates"
t0 = time.time()


def main(yol, j, uret):
    ham = open(yol, "rb").read()
    U = json.loads(ham)
    n, K = U["n"], U["K"]
    D = 1 << n
    x = np.arange(D)
    pc = np.zeros(D, dtype=np.int64)
    for i in range(1, D):
        pc[i] = pc[i >> 1] + (i & 1)
    wr = np.array([u for u, _ in U["w"]], dtype=np.int64)
    wi = np.array([v for _, v in U["w"]], dtype=np.int64)
    wmax = max(max(abs(int(u)), abs(int(v))) for u, v in U["w"])
    paul = pauli_listesi(n, 0, j)
    M1 = len(paul)
    dur(M1 == sum(comb(n, k) * 3 ** k for k in range(0, j + 1)), "Pauli count")
    dur((M1 + 1) * wmax * wmax < SINIR, "G overflow")
    B = np.zeros((2 * D, M1 + 1), dtype=np.int64)
    for k, e in enumerate(paul):
        a, b, ny = maske(e)
        sgn = 1 - 2 * (pc[b & x] & 1)
        ur, ui = i_kuvvet(ny, sgn * wr, sgn * wi)
        B[x ^ a, k] = ur
        B[D + (x ^ a), k] = ui
    B[:D, M1] = -wi; B[D:, M1] = wr                       # i w
    G = B @ B.T
    Nw = sum(int(u) ** 2 + int(v) ** 2 for u, v in U["w"])
    dur(sum(int(v) for v in np.diag(G)) == (M1 + 1) * Nw, "tr(G) ≠ (M_j+2) w†w")
    if uret:
        lmin = float(np.linalg.eigvalsh(G.astype(float))[0])
        t = int(lmin * 0.5)
        Gmax = int(np.abs(G.astype(object)).max())
        f = 0
        while (1 << (2 * (f + 1))) * (Gmax + t) < SINIR // 2:
            f += 1
        out = {"aciklama": "U8 R(j) sertifikası (t, f). U1 sertifikasıyla (sha256) okunur.", "u1_sertifika": yol,
               "u1_sha256": hashlib.sha256(ham).hexdigest(), "n": n, "j": j, "t_G": t, "f_G": f,
               "bilgi": {"lmin_float": lmin}}
        ad = f"{KOK}/R/R_n{n}_K{K}_j{j}_t{U['bilgi']['tohum']}.json"
        json.dump(out, open(ad, "w"), ensure_ascii=False, indent=1)
        print(f"written: {ad}; λ_min≈{lmin:.4e}, t={t}, f={f}")
        return
    CC = json.load(open(f"{KOK}/R/R_n{n}_K{K}_j{j}_t{U['bilgi']['tohum']}.json"))
    dur(CC["u1_sha256"] == hashlib.sha256(ham).hexdigest() and CC["j"] == j, "R certificate does not match")
    print(f"R({j}) certificate, U1 (S certificate) {yol}: n={n}, K={K}, D={D}; M_j+2 = {M1+1} columns")
    # (V1)-(V2): theta, r^2, A > 0 -- the steps of verify_C1 (H is rebuilt in integers)
    et, ck = U["etiketler"], U["katsayilar"]
    dur(all(isinstance(c, int) and c != 0 for c in ck) and len(set(et)) == len(et), "coefficients/labels")
    satir_ust = sum(abs(c) for c in ck)
    dur(2 * satir_ust * wmax < SINIR, "Hw overflow")
    HR = np.zeros((D, D), dtype=np.int64); HI = np.zeros((D, D), dtype=np.int64)
    for e, c in zip(et, ck):
        dur(len(e) == n and 1 <= sum(ch != "I" for ch in e) <= K, f"label {e}")
        a, b, ny = maske(e)
        sgn = 1 - 2 * (pc[b & x] & 1)
        ur, ui = i_kuvvet(ny, c * sgn, np.zeros(D, dtype=np.int64))
        HR[x ^ a, x] += ur; HI[x ^ a, x] += ui
    dur(np.array_equal(HR, HR.T) and np.array_equal(HI, -HI.T), "H is not Hermitian")
    Hwr = [int(v) for v in HR @ wr - HI @ wi]; Hwi = [int(v) for v in HR @ wi + HI @ wr]
    a_ = [int(v) for v in wr]; b_ = [int(v) for v in wi]
    pay = sum(p * r + q * s for p, q, r, s in zip(a_, b_, Hwr, Hwi))
    dur(sum(p * s - q * r for p, q, r, s in zip(a_, b_, Hwr, Hwi)) == 0, "w†Hw is not real")
    theta = Fraction(pay, Nw); s = U["s"]
    dur(theta > s, "θ ≤ s")
    r2 = Fraction(sum(r * r + q * q for r, q in zip(Hwr, Hwi)), Nw) - theta ** 2
    zr = np.array([u for u, _ in U["z"]], dtype=np.int64); zi = np.array([v for _, v in U["z"]], dtype=np.int64)
    q = U["q"]; p = sum(int(u) ** 2 + int(v) ** 2 for u, v in U["z"])
    zmax = max(max(abs(int(u)), abs(int(v))) for u, v in U["z"])
    dur(q > 0 and p > 0 and p * (abs(s) + satir_ust) + 2 * q * zmax * zmax < SINIR, "A overflow")
    AR = p * (s * np.eye(D, dtype=np.int64) - HR) + q * (np.outer(zr, zr) + np.outer(zi, zi))
    AI = -p * HI + q * (np.outer(zi, zr) - np.outer(zr, zi))
    psd_kesin(np.block([[AR, -AI], [AI, AR]]), U["t_A"], U["f_A"], "A")
    print(f"  (V1–V2) θ = {float(theta):.4f} > s = {s} > λ₂ ✓; r̂ = {float(r2)**0.5:.4e}")
    tau = psd_kesin(G, CC["t_G"], CC["f_G"], "G_R")
    sol = 2 * (M1 + 1) * r2 / (theta - s) ** 2
    sag = tau / Nw
    print(f"  (V4R) 2(M_j+2) r̂²/(θ−s)² = {float(sol):.4e} < τ'/w†w = {float(sag):.4e}")
    dur(sol < sag, "Davis–Kahan transfer insufficient")
    print(f"ALL PASSED: R({j}) holds at ψ₀ (n={n}); σ_2D(B_ψ₀) ≥ {float(sag)**0.5 - float(sol)**0.5:.5f}  [{time.time()-t0:.1f} s]")


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), "--uret" in sys.argv)
