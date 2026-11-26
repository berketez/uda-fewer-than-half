"""Exact verifier 1 for C(n,K') certificates (int64 + Python integers; floating point only for the Cholesky HINT).

Statement. psi_0 := top eigenvector of H = sum c_P P (taken from the S certificate). If the following hold, then
span_C{P psi_0 : 0 <= |P| <= K'} = C^D, i.e. C(n,K') holds at psi_0:
  (V1) theta := w^dag H w / w^dag w > s                                     [exact]       => lambda_1 > s
  (V2) A := p(sI - H) + q z z^dag > 0,  p = z^dag z                          [residual]    => lambda_2 < s
  (V3) G := sum_{0<=|P|<=K'} (Pw)(Pw)^dag >= tau' I  (complex Hermitian; via its real embedding)   [residual]
  (V4) 2(M'+1) r^2 / (theta - s)^2 < tau' / w^dag w,   r^2 = ||Hw||^2/w^dag w - theta^2   [exact, Fraction]
Proof: ||psi_0 - w_hat|| <= sqrt(2) r/(theta - s) (Davis-Kahan); for B^C_psi := [P psi]_{0<=|P|<=K'},
||B^C_psi0 - B^C_what||_2 <= ||.||_F = sqrt(M'+1) ||psi_0 - w_hat||; sigma_D(B^C_what)^2 = lambda_min(G)/w^dag w
>= tau'/w^dag w; Weyl => sigma_D(B^C_psi0) > 0.
int64 overflow is excluded in advance at every step with Python integers (partial sums < 2^62, including the
X - tI precondition).
Paulis: bit masks, P|x> = i^{#Y} (-1)^{popcount(b AND x)} |x XOR a>  (label[j] -> qubit j = bit j of x).
The C certificate refers to its S certificate by path ("u1_sertifika") and by SHA-256 ("u1_sha256").
Usage: python3 verify_C1.py <C certificate json>     (run from the package root)
"""
import sys, json, hashlib, itertools, time
from fractions import Fraction
from math import comb
import numpy as np

SINIR = 1 << 62
t0 = time.time()
rng = np.random.default_rng(7)


def dur(kosul, mesaj):
    if not kosul:
        print("FAILED:", mesaj, flush=True)
        sys.exit(1)


def maske(e):
    a = b = ny = 0
    for j, ch in enumerate(e):
        dur(ch in "IXYZ", f"invalid letter {ch}")
        if ch in "XY":
            a |= 1 << j
        if ch in "ZY":
            b |= 1 << j
        ny += ch == "Y"
    return a, b, ny


def i_kuvvet(k, ur, ui):          # i^k (ur + i ui)
    k %= 4
    if k == 0:
        return ur, ui
    if k == 1:
        return -ui, ur
    if k == 2:
        return -ur, -ui
    return ui, -ur


def psd_kesin(X, t, f, ad):
    """X int64 symmetric: proof of X >= (t - ||E||_inf/2^{2f}) I; E = 2^{2f}(X - tI) - R R^T (R integer, a hint)."""
    N = X.shape[0]
    dur(X.dtype == np.int64 and np.array_equal(X, X.T), f"{ad}: not int64 symmetric")
    dur(isinstance(t, int) and isinstance(f, int) and t > 0 and 0 <= f <= 30, f"{ad}: invalid t, f")
    Xmax = int(np.abs(X.astype(object)).max())
    dur(Xmax + t < SINIR, f"{ad}: overflow precondition for X − tI")
    Y = X - t * np.eye(N, dtype=np.int64)
    Ymax = int(np.abs(Y.astype(object)).max())
    dur(Ymax * (1 << (2 * f)) < SINIR, f"{ad}: scaling overflow")
    S = Y * (1 << (2 * f))
    try:
        L = np.linalg.cholesky(Y.astype(float))       # hint only
    except np.linalg.LinAlgError:
        dur(False, f"{ad}: Cholesky hint could not be produced (X − tI does not look positive definite)")
    Lf = np.rint(L * 2.0 ** f)
    dur(np.abs(Lf).max() < 2.0 ** 62, f"{ad}: hint too large")
    R = Lf.astype(np.int64)
    satir2 = max(sum(int(v) * int(v) for v in r) for r in R)
    dur(satir2 < SINIR, f"{ad}: row-norm overflow of R")      # Cauchy-Schwarz => partial sums of R R^T < 2^62
    RR = R @ R.T
    for _ in range(20):                                      # spot check (Python integers)
        i, j = int(rng.integers(N)), int(rng.integers(N))
        dur(sum(int(u) * int(v) for u, v in zip(R[i], R[j])) == int(RR[i, j]), f"{ad}: RRᵀ spot check")
    E = S - RR                                               # |S|, |R R^T| < 2^62 => |E| < 2^63
    Emax = int(np.abs(E.astype(object)).max())
    dur(Emax * N < SINIR, f"{ad}: overflow of residual row sums")
    Einf = int(np.abs(E).sum(axis=1).max())
    alt = Fraction((1 << (2 * f)) * t - Einf, 1 << (2 * f))
    print(f"  {ad}: N={N}, t={t}, f={f}, ‖E‖_∞={Einf} vs 2^(2f)t={(1 << 2*f)*t} (ratio {Einf/((1 << 2*f)*t):.3e})"
          f"  ⇒ λ_min({ad}) ≥ {float(alt):.6e}  [{time.time()-t0:.1f} s]", flush=True)
    dur(alt > 0, f"{ad}: positivity could not be proven")
    return alt


def pauli_listesi(n, Kmin, Kmax):
    out = []
    for agr in range(Kmin, Kmax + 1):
        for yer in itertools.combinations(range(n), agr):
            for h in itertools.product("XYZ", repeat=agr):
                e = ["I"] * n
                for j, c in zip(yer, h):
                    e[j] = c
                out.append("".join(e))
    return out


def main(cyol):
    CC = json.load(open(cyol))
    ham = open(CC["u1_sertifika"], "rb").read()
    dur(hashlib.sha256(ham).hexdigest() == CC["u1_sha256"], "sha256 of the S (U1) certificate does not match")
    U = json.loads(ham)
    n, K, Kp = U["n"], U["K"], CC["Kp"]
    dur(CC["n"] == n and 1 <= Kp <= n, "n / K' inconsistent")
    D = 1 << n
    x = np.arange(D)
    pc = np.zeros(D, dtype=np.int64)
    for i in range(1, D):
        pc[i] = pc[i >> 1] + (i & 1)
    print(f"C certificate {cyol}\n  U1 (S certificate): {CC['u1_sertifika']} (sha256 matches); n={n}, K={K}, target C(n,{Kp}), D={D}")
    # (V0) H
    et, ck = U["etiketler"], U["katsayilar"]
    dur(len(et) == len(ck) and len(set(et)) == len(et), "label list")
    dur(all(isinstance(c, int) and c != 0 for c in ck), "coefficients are not nonzero integers")
    satir_ust = sum(abs(c) for c in ck)
    dur(satir_ust < SINIR, "coefficient sum")
    HR = np.zeros((D, D), dtype=np.int64)
    HI = np.zeros((D, D), dtype=np.int64)
    for e, c in zip(et, ck):
        dur(len(e) == n and 1 <= sum(ch != "I" for ch in e) <= K, f"label {e}")
        a, b, ny = maske(e)
        sgn = 1 - 2 * (pc[b & x] & 1)
        ur, ui = i_kuvvet(ny, c * sgn, np.zeros(D, dtype=np.int64))
        HR[x ^ a, x] += ur
        HI[x ^ a, x] += ui
    dur(np.array_equal(HR, HR.T) and np.array_equal(HI, -HI.T), "H is not Hermitian")
    # (V1) theta, r^2
    wr = np.array([u for u, _ in U["w"]], dtype=np.int64)
    wi = np.array([v for _, v in U["w"]], dtype=np.int64)
    wmax = max(max(abs(int(u)), abs(int(v))) for u, v in U["w"])          # Python integer (no int64 abs overflow)
    dur(2 * satir_ust * wmax < SINIR, "Hw overflow")
    Hwr = HR @ wr - HI @ wi
    Hwi = HR @ wi + HI @ wr
    L = lambda v: [int(u) for u in v]
    a_, b_, c_, d_ = L(wr), L(wi), L(Hwr), L(Hwi)
    pay = sum(p * r + q * s_ for p, q, r, s_ in zip(a_, b_, c_, d_))
    sanal = sum(p * s_ - q * r for p, q, r, s_ in zip(a_, b_, c_, d_))
    Nw = sum(p * p + q * q for p, q in zip(a_, b_))
    Hw2 = sum(r * r + s_ * s_ for r, s_ in zip(c_, d_))
    dur(sanal == 0, "w†Hw is not real")
    s = U["s"]
    theta = Fraction(pay, Nw)
    dur(theta > s, "θ ≤ s")
    r2 = Fraction(Hw2, Nw) - theta * theta
    dur(r2 >= 0, "r̂² < 0 (internal inconsistency)")
    print(f"  (V1) θ = {float(theta):.6f} > s = {s}; r̂ = {float(r2)**0.5:.6e}   [exact]")
    # (V2) lambda_2 < s
    zr = np.array([u for u, _ in U["z"]], dtype=np.int64)
    zi = np.array([v for _, v in U["z"]], dtype=np.int64)
    q = U["q"]
    p = sum(int(u) * int(u) + int(v) * int(v) for u, v in zip(zr, zi))
    zmax = max(max(abs(int(u)), abs(int(v))) for u, v in U["z"])
    dur(q > 0 and p > 0, "p, q")
    dur(p * (abs(s) + satir_ust) + 2 * q * zmax * zmax < SINIR, "A overflow")
    AR = p * (s * np.eye(D, dtype=np.int64) - HR) + q * (np.outer(zr, zr) + np.outer(zi, zi))
    AI = -p * HI + q * (np.outer(zi, zr) - np.outer(zr, zi))
    Ae = np.block([[AR, -AI], [AI, AR]])
    del AR, AI, HR, HI
    psd_kesin(Ae, U["t_A"], U["f_A"], "A")
    del Ae
    print(f"  (V2) A ≻ 0 ⇒ λ₂(H) < s; λ₁ > s > λ₂: ψ₀ is well defined and simple.")
    # (V3) G = sum (Pw)(Pw)^dag, 0 <= |P| <= K'
    paul = pauli_listesi(n, 0, Kp)
    M1 = len(paul)
    dur(M1 == sum(comb(n, k) * 3 ** k for k in range(0, Kp + 1)) and len(set(paul)) == M1, "Pauli count")
    dur(2 * M1 * wmax * wmax < SINIR, "G overflow")
    Br = np.zeros((D, M1), dtype=np.int64)
    Bi = np.zeros((D, M1), dtype=np.int64)
    for k, e in enumerate(paul):
        a, b, ny = maske(e)
        sgn = 1 - 2 * (pc[b & x] & 1)
        ur, ui = i_kuvvet(ny, sgn * wr, sgn * wi)
        Br[x ^ a, k] = ur
        Bi[x ^ a, k] = ui
    GR = Br @ Br.T + Bi @ Bi.T
    GI = Bi @ Br.T - Br @ Bi.T
    for _ in range(20):
        i, j = int(rng.integers(D)), int(rng.integers(D))
        tr = sum(int(Br[i, k]) * int(Br[j, k]) + int(Bi[i, k]) * int(Bi[j, k]) for k in range(M1))
        ti = sum(int(Bi[i, k]) * int(Br[j, k]) - int(Br[i, k]) * int(Bi[j, k]) for k in range(M1))
        dur(tr == int(GR[i, j]) and ti == int(GI[i, j]), "G spot check")
    dur(np.array_equal(GR, GR.T) and np.array_equal(GI, -GI.T), "G is not Hermitian")
    tr_G = sum(int(v) for v in np.diag(GR))
    dur(tr_G == M1 * Nw, "tr(G) ≠ (M'+1) w†w")        # every column has ||Pw||^2 = w^dag w
    del Br, Bi
    X = np.block([[GR, -GI], [GI, GR]])
    print(f"  (V3) G built: M'+1 = {M1} Paulis (I included, |P| ≤ {Kp}); tr(G) = (M'+1)·w†w holds; spot checks 20/20"
          f"  [{time.time()-t0:.1f} s]", flush=True)
    tau = psd_kesin(X, CC["t_G"], CC["f_G"], "G")
    # (V4) transfer
    sol = 2 * M1 * r2 / (theta - s) ** 2
    sag = tau / Nw
    print(f"  (V4) 2(M'+1) r̂²/(θ−s)² = {float(sol):.4e}  <  τ'/w†w = {float(sag):.4e}  (ratio {float(sol/sag):.3e})")
    dur(sol < sag, "Davis–Kahan transfer insufficient")
    print(f"      ⇒ σ_D(B^C_ψ₀) ≥ {float(sag)**0.5 - float(sol)**0.5:.5f} > 0")
    print(f"ALL PASSED: C({n},{Kp}) holds at ψ₀ (span_C{{Pψ₀ : |P| ≤ {Kp}}} = C^{D}).  [{time.time()-t0:.1f} s]")


if __name__ == "__main__":
    main(sys.argv[1])
