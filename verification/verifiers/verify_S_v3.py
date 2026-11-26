"""Final verifier (v3) for S(n,K) certificates.

Reads only the certificate JSON; it does not use any of the code that produced the certificate.

Checked statements:
  (D0) Format: every label is a Pauli string of weight 1 <= |P| <= K; coefficients are integers. H = sum c_P P.
  (D1) theta := w^dag H w / w^dag w > s                    (exact integer/rational)   => lambda_1(H) > s
  (D2) A := p(sI - H) + q z z^dag > 0, p = z^dag z         (integer-residual Cholesky) => lambda_2(H) < s
       => lambda_1 is simple; psi_0 := top eigenvector, which is UDA with its K-body marginals.
  (D3) G := B_w B_w^T >= tau' I; columns of B_w: real embeddings of P w (all 1 <= |P| <= K), w, i w.
  (D4) 2(M+2) r^2 / (theta - s)^2 < tau' / w^dag w  (r = ||H w_hat - theta w_hat||, w_hat = w/||w||)  (rational)
       => sigma_min(B_psi0) > 0 => rank_R{Pi_perp P psi_0} = 2D - 2 => the UDA states contain a nonempty open set.
Floating point is used ONLY to produce the Cholesky hint L. The verdict rests on the integer residual
E = 2^{2f}(X - tI) - R R^T (R = round(2^f L)); a bad hint can at worst make the check FAIL, never produce a
false PASS. int64 overflow is excluded at every step by an explicit bound (|intermediate sum| <= 2^62).
--blas mode (large n): the integer matrix products are computed with floating-point GEMM. Before each product
it is proven in exact integers (Cauchy-Schwarz) that every intermediate sum has absolute value < 2^53. Then
every intermediate result is an exactly represented integer and the GEMM result is exact. Assumption: GEMM
uses only additions and multiplications (the property that Ozaki-type error-free products rely on).
Extra safeguard: randomly chosen entries are recomputed with Python integers.

History of this version: two int64 overflow gaps of earlier versions are closed here:
 (i) psd_kesin and psd_kesin_blas check, in Python integers, that X - tI cannot wrap before it is formed;
 (ii) p = z^dag z in (D2) is computed with Python integers (an int64 sum of squares could wrap, and the
      "A overflow" check used the wrapped value). Counterexample for (ii): certificates/negative/S_overflow_p.json.
Usage: python3 verify_S_v3.py certificate.json [--blas]
"""
import sys, json, itertools, time
from fractions import Fraction
from math import comb
import numpy as np

SINIR = 1 << 62
BLAS = "--blas" in sys.argv
B53 = 1 << 53
rng = np.random.default_rng(12345)
t0 = time.time()


def dur(kosul, mesaj):
    if not kosul:
        print("FAILED:", mesaj)
        sys.exit(1)


def maske(etiket):
    a = b = ny = 0
    for j, ch in enumerate(etiket):
        dur(ch in "IXYZ", f"invalid letter {ch}")
        if ch in "XY":
            a |= 1 << j
        if ch in "ZY":
            b |= 1 << j
        ny += ch == "Y"
    return a, b, ny        # P|x> = i^ny (-1)^{popcount(b AND x)} |x XOR a>   (Y = iXZ)


def i_kuvvet(k, ur, ui):   # i^k (ur + i ui)
    return [(ur, ui), (-ui, ur), (-ur, -ui), (ui, -ur)][k % 4]


def psd_kesin(X, t, f, ad):
    """Prove X >= (t - ||E||_inf/2^{2f}) I for a symmetric int64 X; return the lower bound as a Fraction."""
    N = X.shape[0]
    dur(np.array_equal(X, X.T), f"{ad}: not symmetric")
    dur(t > 0 and f >= 0, f"{ad}: invalid t, f")
    # Precondition (fix (i)): exclude int64 wrap-around of X - tI, checked in Python integers BEFORE forming it.
    dur(int(np.abs(X.astype(object)).max()) + int(t) < SINIR, f"{ad}: overflow precondition for X − tI")
    Y = X - t * np.eye(N, dtype=np.int64)
    dur(int(np.abs(Y).max()) * (1 << (2 * f)) < SINIR, f"{ad}: scaling overflow")
    S = Y * (1 << (2 * f))
    try:
        L = np.linalg.cholesky(Y.astype(float))          # hint only
    except np.linalg.LinAlgError:
        dur(False, f"{ad}: Cholesky hint could not be produced")
    R = np.rint(L * 2.0 ** f).astype(np.int64)
    satir2 = max(sum(int(v) * int(v) for v in r) for r in R)  # exact: max_i ||R_i||^2
    dur(satir2 < SINIR, f"{ad}: row-norm overflow of R")      # Cauchy-Schwarz => partial sums of R R^T < 2^62
    E = S - R @ R.T                                           # exact (no overflow)
    Emax = int(np.abs(E).max())
    dur(Emax * N < SINIR, f"{ad}: residual overflow")
    Einf = int(np.abs(E).sum(axis=1).max())                   # ||E||_2 <= ||E||_inf (E symmetric)
    alt = Fraction((1 << (2 * f)) * t - Einf, 1 << (2 * f))
    print(f"  {ad}: N={N}, t={t}, f={f}, ‖E‖_∞ = {Einf} < 2^(2f)·t = {(1 << 2*f)*t} "
          f"(ratio {Einf/((1 << 2*f)*t):.3e})  ⇒  λ_min({ad}) ≥ {float(alt):.6e}", flush=True)
    dur(alt > 0, f"{ad}: positivity could not be proven")
    return alt


def satir_norm2_tam(R):
    """Squared row norms of an integer-valued R, exactly (int64 chunks + Python summation); returns the maximum."""
    Ri = R.astype(np.int64)
    dur(int(np.abs(Ri).max()) < (1 << 26), "entry of R exceeds 2^26")     # square < 2^52
    top = [0] * Ri.shape[0]
    for j0 in range(0, Ri.shape[1], 1024):                                   # chunk sums < 2^62
        parca = (Ri[:, j0:j0 + 1024] ** 2).sum(axis=1)
        top = [u + int(v) for u, v in zip(top, parca)]
    return max(top)


def psd_kesin_blas(X, t, f, ad):
    """Same statement as psd_kesin; R R^T by GEMM, with all intermediate sums proven < 2^53."""
    # same precondition as in psd_kesin (fix (i))
    dur(int(np.abs(np.asarray(X).astype(object)).max()) + int(t) < SINIR, f"{ad}: overflow precondition for X − tI")
    N = X.shape[0]
    dur(np.array_equal(X, X.T), f"{ad}: not symmetric")
    dur(t > 0 and f >= 0, f"{ad}: invalid t, f")
    dur((int(np.abs(X).max()) + t) * (1 << (2 * f)) < B53, f"{ad}: scale exceeds 2^53")
    Y = X.astype(float)                                   # exact (|X| < 2^53)
    Y[np.arange(N), np.arange(N)] -= t
    try:
        L = np.linalg.cholesky(Y)                         # hint only
    except np.linalg.LinAlgError:
        dur(False, f"{ad}: Cholesky hint could not be produced")
    del Y
    R = np.rint(L * 2.0 ** f)
    del L
    satir2 = satir_norm2_tam(R)
    dur(satir2 < B53, f"{ad}: row norm of R ≥ 2^53")    # => every partial sum of R R^T < 2^53 => GEMM exact
    Einf, Emax, nokta = 0, 0, 0
    for i0 in range(0, N, 1024):
        blk = R[i0:i0 + 1024] @ R.T
        Bi = blk.astype(np.int64)
        for _ in range(4):                                # spot check: recomputed with Python integers
            a_, b_ = int(rng.integers(Bi.shape[0])), int(rng.integers(N))
            tam = sum(int(u) * int(v) for u, v in zip(R[i0 + a_], R[b_]))
            dur(tam == int(Bi[a_, b_]), f"{ad}: GEMM spot check failed")
            nokta += 1
        S = X[i0:i0 + 1024].copy()
        nb = S.shape[0]
        S[np.arange(nb), i0 + np.arange(nb)] -= t
        S *= (1 << (2 * f))
        E = S - Bi
        Emax = max(Emax, int(np.abs(E).max()))
        dur(Emax * N < SINIR, f"{ad}: residual overflow")
        Einf = max(Einf, int(np.abs(E).sum(axis=1).max()))
    alt = Fraction((1 << (2 * f)) * t - Einf, 1 << (2 * f))
    print(f"  {ad}: N={N}, t={t}, f={f}, ‖E‖_∞ = {Einf} < 2^(2f)·t = {(1 << 2*f)*t} "
          f"(ratio {Einf/((1 << 2*f)*t):.3e}); GEMM spot checks {nokta}/{nokta}  ⇒  λ_min({ad}) ≥ {float(alt):.6e}",
          flush=True)
    dur(alt > 0, f"{ad}: positivity could not be proven")
    return alt


def main(yol):
    C = json.load(open(yol))
    n, K = C["n"], C["K"]
    D = 1 << n
    x = np.arange(D)
    pc = np.zeros(D, dtype=np.int64)
    for i in range(1, D):
        pc[i] = pc[i >> 1] + (i & 1)
    print(f"Certificate {yol}: n = {n}, K = {K}, D = {D}, mode = {'GEMM-exact (--blas)' if BLAS else 'int64'}")
    # (D0) build H in integers
    et, ck = C["etiketler"], C["katsayilar"]
    dur(len(et) == len(ck) and len(set(et)) == len(et), "label list")
    dur(all(isinstance(c, int) and c != 0 for c in ck), "coefficients are not nonzero integers")
    dur(sum(abs(c) for c in ck) < SINIR, "coefficient-sum overflow")
    HR = np.zeros((D, D), dtype=np.int64)
    HI = np.zeros((D, D), dtype=np.int64)
    for e, c in zip(et, ck):
        dur(len(e) == n, "label length")
        agirlik = sum(ch != "I" for ch in e)
        dur(1 <= agirlik <= K, f"weight {agirlik} ∉ [1, K]: {e}")
        a, b, ny = maske(e)
        sgn = 1 - 2 * (pc[b & x] & 1)
        ur, ui = i_kuvvet(ny, c * sgn, np.zeros(D, dtype=np.int64))
        HR[x ^ a, x] += ur
        HI[x ^ a, x] += ui
    dur(np.array_equal(HR, HR.T) and np.array_equal(HI, -HI.T), "H is not Hermitian")
    print(f"  (D0) H = Σ c_P P built: {len(et)} Paulis, weights ≤ {K}, Hermitian, max|c| = {max(map(abs, ck))}")
    # (D1) Rayleigh quotient
    wr = np.array([u for u, _ in C["w"]], dtype=np.int64)
    wi = np.array([v for _, v in C["w"]], dtype=np.int64)
    zr = np.array([u for u, _ in C["z"]], dtype=np.int64)
    zi = np.array([v for _, v in C["z"]], dtype=np.int64)
    satir_abs = int(max(np.abs(HR).sum(axis=1).max(), np.abs(HI).sum(axis=1).max()))
    dur(2 * satir_abs * int(max(np.abs(wr).max(), np.abs(wi).max())) < SINIR, "Hw overflow")
    Hw_r = HR @ wr - HI @ wi
    Hw_i = HR @ wi + HI @ wr
    py = lambda v: [int(u) for u in v]
    wr_, wi_, hr_, hi_ = py(wr), py(wi), py(Hw_r), py(Hw_i)
    pay = sum(a * c + b * d for a, b, c, d in zip(wr_, wi_, hr_, hi_))          # Re w^dag H w
    sanal = sum(a * d - b * c for a, b, c, d in zip(wr_, wi_, hr_, hi_))        # Im w^dag H w
    payda = sum(a * a + b * b for a, b in zip(wr_, wi_))                         # w^dag w
    Hw2 = sum(c * c + d * d for c, d in zip(hr_, hi_))                           # ||Hw||^2
    dur(sanal == 0, "w†Hw is not real")
    s = C["s"]
    theta = Fraction(pay, payda)
    dur(theta > s, "θ ≤ s")
    print(f"  (D1) θ = w†Hw/w†w = {float(theta):.6f} > s = {s}  ⇒  λ₁(H) ≥ θ > s   [exact]")
    # (D2) A = p(sI - H) + q z z^dag > 0
    q = C["q"]
    # fix (ii): p in Python integers; the int64 sum of squares could overflow.
    p = sum(int(a) * int(a) + int(b) * int(b) for a, b in zip(zr, zi))
    dur(p < SINIR, "p = z†z overflow")
    dur(q > 0 and p > 0, "p, q")
    dur(p * (abs(s) + satir_abs) + q * p < SINIR, "A overflow")
    AR = p * (s * np.eye(D, dtype=np.int64) - HR) + q * (np.outer(zr, zr) + np.outer(zi, zi))
    AI = -p * HI + q * (np.outer(zi, zr) - np.outer(zr, zi))
    Ae = np.block([[AR, -AI], [AI, AR]])          # Hermitian -> real symmetric; eigenvalues doubled
    del HR, HI, AR, AI
    altA = (psd_kesin_blas if BLAS else psd_kesin)(Ae, C["t_A"], C["f_A"], "A")
    del Ae
    print(f"  (D2) A ≻ 0  ⇒  H ≺ sI + (q/p) zz†  ⇒  λ₂(H) < s.  Together: λ₁ > s > λ₂, λ₁ is SIMPLE.")
    # (D3) G = B_w B_w^T >= tau' I  (all Paulis with 1 <= |P| <= K)
    tum = []
    for agr in range(1, K + 1):
        for dest in itertools.combinations(range(n), agr):
            for harfler in itertools.product("XYZ", repeat=agr):
                e = ["I"] * n
                for j, h in zip(dest, harfler):
                    e[j] = h
                tum.append("".join(e))
    M = len(tum)
    dur(M == sum(comb(n, k) * 3 ** k for k in range(1, K + 1)) and len(set(tum)) == M, "Pauli count")
    wmax = int(max(np.abs(wr).max(), np.abs(wi).max()))
    dur((M + 2) * wmax * wmax < SINIR, "G overflow")      # |partial sum| <= sum|u_a u_b| <= (M+2) wmax^2
    G = np.zeros((2 * D, 2 * D), dtype=float if BLAS else np.int64)
    if BLAS:
        dur((M + 2) * wmax * wmax < B53, "G: GEMM exactness bound")   # every partial sum < 2^53
    sutun = [np.concatenate([wr, wi]), np.concatenate([-wi, wr])]   # w and i w
    kayit_i = [int(u) for u in rng.integers(2 * D, size=6)]
    kayit = []                                                     # rows kept for the spot check
    def bosalt(sut):
        nonlocal G
        Bk = np.array(sut, dtype=float if BLAS else np.int64).T
        kayit.append(Bk[kayit_i].astype(np.int64))
        G += Bk @ Bk.T
    for e in tum:
        a, b, ny = maske(e)
        sgn = 1 - 2 * (pc[b & x] & 1)
        ur, ui = i_kuvvet(ny, sgn * wr, sgn * wi)
        cr = np.zeros(D, dtype=np.int64); ci = np.zeros(D, dtype=np.int64)
        cr[x ^ a] = ur; ci[x ^ a] = ui
        sutun.append(np.concatenate([cr, ci]))
        if len(sutun) >= 2048:
            bosalt(sutun); sutun = []
    if sutun:
        bosalt(sutun)
    if BLAS:
        G = G.astype(np.int64)
    Ksec = np.hstack(kayit)
    for u in range(len(kayit_i)):
        for v in range(len(kayit_i)):
            tam = sum(int(a) * int(b) for a, b in zip(Ksec[u], Ksec[v]))
            dur(tam == int(G[kayit_i[u], kayit_i[v]]), "G spot check failed")
    print(f"  (D3) G_w = B_w B_wᵀ built in exact integers (M = {M} Paulis + w, iw; {'GEMM-exact' if BLAS else 'int64'}; "
          f"spot checks {len(kayit_i)**2}/{len(kayit_i)**2})  [{time.time()-t0:.1f} s]")
    altG = (psd_kesin_blas if BLAS else psd_kesin)(G, C["tau"], C["f_G"], "G")
    # (D4) Davis-Kahan transfer
    r2 = Fraction(Hw2, payda) - theta * theta          # r^2 = ||H w_hat - theta w_hat||^2
    sol = 2 * (M + 2) * r2 / (theta - s) ** 2          # >= (M+2)||psi_0 - w_hat||^2 >= ||B_psi0 - B_what||_2^2
    sag = altG / payda                                  # <= sigma_min(B_what)^2
    print(f"  (D4) r̂ = {float(r2) ** 0.5:.4e}, θ − s = {float(theta - s):.4f}; "
          f"2(M+2) r̂²/(θ−s)² = {float(sol):.4e} < σ_min(B_ŵ)² ≥ {float(sag):.4e}")
    dur(sol < sag, "Davis–Kahan transfer insufficient")
    print(f"      ⇒ σ_min(B_ψ₀) ≥ {float(sag) ** 0.5 - float(sol) ** 0.5:.4f} > 0  ⇒  rank_ℝ = 2D = {2*D}.")
    print(f"ALL PASSED (n = {n}, K = {K}): ψ₀ is UDA with its K-body marginals; dΦ is onto ⇒ the UDA set contains a "
          f"nonempty open set.  [{time.time()-t0:.1f} s]")


if __name__ == "__main__":
    main(sys.argv[1])
