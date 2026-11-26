"""Second, independently written verifier for C(n,K') certificates (different routes from verify_C1.py).

Differences:
  - Paulis are NOT built with the bit-mask/phase formula but by applying Gaussian-integer 2x2 matrices to the
    tensor axes one by one (np.tensordot). Bit j of x = qubit j = axis (n-1-j) of the C-ordered (2,)*n array.
  - The Pauli set is enumerated by filtering all 4^n labels.
  - G = sum (Pw)(Pw)^dag stays complex Hermitian (NO real embedding); the PD proof uses a complex Cholesky
    hint R (Gaussian integers): E = 2^{2f}(G - tI) - R R^dag, ||E||_2 <= max_i sum_j (|Re E_ij| + |Im E_ij|).
  - n <= 6: in addition, Sylvester's criterion (all leading principal minors > 0) by fraction-free Bareiss
    elimination, on the real embedding of G - tI and on the real embedding of A; entirely Python integers.
  - theta, r^2 and the Davis-Kahan transfer are recomputed with Fraction; Hw with tensor Paulis.
(V2) lambda_2 < s: re-proved here with Bareiss for n <= 6 and with the complex residual method for n = 8; NOT
done here for n = 10 (there it is covered by verify_C1.py and by the S verifier verify_S_v3.py).
Usage: python3 verify_C2.py <C certificate json>     (run from the package root)
"""
import sys, json, hashlib, time
from fractions import Fraction
import numpy as np

SINIR = 1 << 62
t0 = time.time()
# (Re, Im) 2x2 matrices, row-major [[m00, m01], [m10, m11]]
TEK = {"I": (np.array([[1, 0], [0, 1]]), np.array([[0, 0], [0, 0]])),
       "X": (np.array([[0, 1], [1, 0]]), np.array([[0, 0], [0, 0]])),
       "Y": (np.array([[0, 0], [0, 0]]), np.array([[0, -1], [1, 0]])),
       "Z": (np.array([[1, 0], [0, -1]]), np.array([[0, 0], [0, 0]]))}


def dur(k, m):
    if not k:
        print("FAILED:", m, flush=True)
        sys.exit(1)


def tensor_uygula(et, vr, vi, n):
    """vr, vi: (2,)*n int64 (C order). P = tensor product of the label; qubit j <-> axis n-1-j."""
    for j, ch in enumerate(et):
        if ch == "I":
            continue
        mr, mi = TEK[ch]
        ax = n - 1 - j
        ar = np.moveaxis(np.tensordot(mr, vr, axes=([1], [ax])) - np.tensordot(mi, vi, axes=([1], [ax])), 0, ax)
        ai = np.moveaxis(np.tensordot(mr, vi, axes=([1], [ax])) + np.tensordot(mi, vr, axes=([1], [ax])), 0, ax)
        vr, vi = ar, ai
    return vr, vi


def etiket_suz(n, Kp):
    harf = "IXYZ"
    out = []
    for k in range(4 ** n):
        e, kk = [], k
        for _ in range(n):
            e.append(harf[kk & 3]); kk >>= 2
        if sum(c != "I" for c in e) <= Kp:
            out.append("".join(e))
    return out


def bareiss_pd(X):
    A = [[int(v) for v in row] for row in X]
    N = len(A)
    onceki = 1
    for k in range(N):
        if A[k][k] <= 0:
            return False, k
        akk = A[k][k]
        for i in range(k + 1, N):
            aik = A[i][k]
            Ai, Ak = A[i], A[k]
            for j in range(k + 1, N):
                Ai[j] = (Ai[j] * akk - aik * Ak[j]) // onceki
        onceki = akk
    return True, N


def gercel_gomme(GR, GI):
    return np.block([[GR, -GI], [GI, GR]])


def karmasik_psd(GR, GI, t, f, ad):
    """G = GR + i GI Hermitian (int64). G >= (t - ||E||/2^{2f}) I; R Gaussian integers (complex Cholesky hint)."""
    N = GR.shape[0]
    dur(np.array_equal(GR, GR.T) and np.array_equal(GI, -GI.T), f"{ad}: not Hermitian")
    dur(isinstance(t, int) and t > 0 and 0 <= f <= 30, f"{ad}: invalid t, f")
    m = max(int(np.abs(GR.astype(object)).max()), int(np.abs(GI.astype(object)).max()))
    dur(m + t < SINIR and (m + t) * (1 << (2 * f)) < SINIR, f"{ad}: scaling overflow")
    YR = GR - t * np.eye(N, dtype=np.int64)
    try:
        L = np.linalg.cholesky(YR.astype(float) + 1j * GI.astype(float))
    except np.linalg.LinAlgError:
        dur(False, f"{ad}: complex Cholesky hint could not be produced")
    Rr = np.rint(L.real * 2.0 ** f).astype(np.int64)
    Ri = np.rint(L.imag * 2.0 ** f).astype(np.int64)
    n2 = 0
    for a, b in zip(Rr, Ri):
        n2 = max(n2, sum(int(u) * int(u) for u in a) + sum(int(u) * int(u) for u in b))
    dur(n2 < SINIR, f"{ad}: row-norm overflow of R")
    RRr = Rr @ Rr.T + Ri @ Ri.T          # Re(R R^dag)
    RRi = Ri @ Rr.T - Rr @ Ri.T          # Im(R R^dag)
    Er = YR * (1 << (2 * f)) - RRr
    Ei = GI * (1 << (2 * f)) - RRi
    e_ust = max(int(np.abs(Er.astype(object)).max()), int(np.abs(Ei.astype(object)).max()))
    dur(2 * N * e_ust < SINIR, f"{ad}: overflow of residual sums")
    Enorm = int((np.abs(Er) + np.abs(Ei)).sum(axis=1).max())
    alt = Fraction((1 << (2 * f)) * t - Enorm, 1 << (2 * f))
    print(f"  {ad} (complex residual): N={N}, t={t}, f={f}, ‖E‖≤{Enorm} vs 2^(2f)t={(1 << 2*f)*t} "
          f"(ratio {Enorm/((1 << 2*f)*t):.3e}) ⇒ λ_min ≥ {float(alt):.6e}  [{time.time()-t0:.1f} s]", flush=True)
    dur(alt > 0, f"{ad}: positivity could not be proven")
    return alt


def main(cyol):
    CC = json.load(open(cyol))
    ham = open(CC["u1_sertifika"], "rb").read()
    dur(hashlib.sha256(ham).hexdigest() == CC["u1_sha256"], "sha256")
    U = json.loads(ham)
    n, K, Kp = U["n"], U["K"], CC["Kp"]
    D = 1 << n
    sh = (2,) * n
    print(f"[verify_C2] {cyol}: n={n}, K={K}, target C(n,{Kp})")
    wr = np.array([u for u, _ in U["w"]], dtype=np.int64).reshape(sh)
    wi = np.array([v for _, v in U["w"]], dtype=np.int64).reshape(sh)
    wmax = max(max(abs(int(u)), abs(int(v))) for u, v in U["w"])          # Python integer
    # Hw (tensor Paulis), accumulated in Python integers
    ck = U["katsayilar"]
    dur(all(isinstance(c, int) for c in ck), "coefficients")
    dur(sum(abs(c) for c in ck) * 2 * wmax < SINIR, "Hw overflow")
    hr = np.zeros(D, dtype=np.int64); hi = np.zeros(D, dtype=np.int64)
    for e, c in zip(U["etiketler"], ck):
        dur(1 <= sum(ch != "I" for ch in e) <= K and len(e) == n, "label")
        pr, pi = tensor_uygula(e, wr, wi, n)
        hr += c * pr.reshape(D); hi += c * pi.reshape(D)
    a_ = [int(v) for v in wr.reshape(D)]; b_ = [int(v) for v in wi.reshape(D)]
    c_ = [int(v) for v in hr]; d_ = [int(v) for v in hi]
    Nw = sum(p * p + q * q for p, q in zip(a_, b_))
    re_ = sum(p * r + q * s for p, q, r, s in zip(a_, b_, c_, d_))
    im_ = sum(p * s - q * r for p, q, r, s in zip(a_, b_, c_, d_))
    h2 = sum(r * r + s * s for r, s in zip(c_, d_))
    dur(im_ == 0, "w†Hw is not real")
    theta = Fraction(re_, Nw)
    s = U["s"]
    dur(theta > s, "θ ≤ s")
    r2 = Fraction(h2, Nw) - theta ** 2
    print(f"  θ = {float(theta):.6f} > s = {s}; r̂ = {float(r2)**0.5:.6e}  [exact; tensor Paulis]")
    # (V2) lambda_2 < s
    if n <= 8:
        HRm = np.zeros((D, D), dtype=np.int64); HIm = np.zeros((D, D), dtype=np.int64)
        for e, c in zip(U["etiketler"], ck):
            Pr, Pi = np.array([[1]], dtype=np.int64), np.array([[0]], dtype=np.int64)
            for ch in e:       # e[0] = qubit 0 = least significant bit => rightmost in the Kronecker product
                mr, mi = TEK[ch]
                Pr, Pi = np.kron(mr, Pr) - np.kron(mi, Pi), np.kron(mr, Pi) + np.kron(mi, Pr)
            HRm += c * Pr; HIm += c * Pi
        # is the Kronecker H consistent with the tensor Hw?
        dur(np.array_equal(HRm @ wr.reshape(D) - HIm @ wi.reshape(D), hr) and
            np.array_equal(HRm @ wi.reshape(D) + HIm @ wr.reshape(D), hi), "Kronecker H ≠ tensor H")
        zr = np.array([u for u, _ in U["z"]], dtype=np.int64); zi = np.array([v for _, v in U["z"]], dtype=np.int64)
        p = sum(int(u) ** 2 + int(v) ** 2 for u, v in U["z"]); q = U["q"]   # Python integers (NO int64 sum)
        zmax = max(max(abs(int(u)), abs(int(v))) for u, v in U["z"])
        dur(isinstance(q, int) and q > 0 and p > 0, "p, q")
        dur(p * (abs(s) + sum(abs(c) for c in ck)) + 2 * q * zmax * zmax < SINIR, "A overflow")
        AR = p * (s * np.eye(D, dtype=np.int64) - HRm) + q * (np.outer(zr, zr) + np.outer(zi, zi))
        AI = -p * HIm + q * (np.outer(zi, zr) - np.outer(zr, zi))
        if n <= 6:
            ok, k = bareiss_pd(gercel_gomme(AR, AI))
            dur(ok, f"A: Bareiss leading minor {k} ≤ 0")
            print(f"  (V2) A ≻ 0: Bareiss/Sylvester, all {2*D} leading minors > 0  [{time.time()-t0:.1f} s]")
        else:
            karmasik_psd(AR, AI, U["t_A"] // 2, U["f_A"] - 1, "A")
            print(f"  (V2) A ≻ 0 (complex residual method)")
    else:
        print("  (V2) n > 8: not done here (covered by verify_C1.py V2 and by the S verifier D2).")
    # (V3) G
    paul = etiket_suz(n, Kp)
    M1 = len(paul)
    dur(2 * M1 * wmax * wmax < SINIR, "G overflow")
    Br = np.zeros((D, M1), dtype=np.int64); Bi = np.zeros((D, M1), dtype=np.int64)
    for k, e in enumerate(paul):
        pr, pi = tensor_uygula(e, wr, wi, n)
        Br[:, k] = pr.reshape(D); Bi[:, k] = pi.reshape(D)
    GR = Br @ Br.T + Bi @ Bi.T
    GI = Bi @ Br.T - Br @ Bi.T
    print(f"  (V3) M'+1 = {M1} labels (filter over 4^{n}); G built  [{time.time()-t0:.1f} s]", flush=True)
    t, f = CC["t_G"], CC["f_G"]
    if n <= 6:
        ok, k = bareiss_pd(gercel_gomme(GR - t * np.eye(D, dtype=np.int64), GI))
        dur(ok, f"G − tI: Bareiss leading minor {k} ≤ 0")
        tau = Fraction(t)                     # Bareiss: lambda_min(G) > t
        print(f"  G − tI ≻ 0: Bareiss/Sylvester ({2*D} leading minors > 0) ⇒ λ_min(G) > t = {t}  [{time.time()-t0:.1f} s]")
        karmasik_psd(GR, GI, t, f, "G")       # extra check (the verdict rests on Bareiss)
    else:
        tau = karmasik_psd(GR, GI, t, f, "G")
    sol = 2 * M1 * r2 / (theta - s) ** 2
    sag = tau / Nw
    print(f"  (V4) lhs = {float(sol):.4e} < rhs = {float(sag):.4e}")
    dur(sol < sag, "Davis–Kahan transfer insufficient")
    print(f"ALL PASSED [verify_C2]: C({n},{Kp}) holds at ψ₀.  [{time.time()-t0:.1f} s]")


if __name__ == "__main__":
    main(sys.argv[1])
