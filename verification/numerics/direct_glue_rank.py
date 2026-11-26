"""Direct numerical check of gluing (FLOATING POINT, indicative only; not a certificate).

psi = psi_a (x) psi_b (psi_a on the low bits, psi_b on the high bits); psi_a, psi_b = top eigenvectors of the
certified integer H's of the S certificates (computed numerically here).
Measured: rank_R V_K, V_K := span_R{P psi : 0 <= |P| <= K} + R i psi  (the rank condition of S(n,K); full = 2D).
Two methods:
  (svd)  singular values of the real 2D x (M_K + 2) matrix (n <= 10);
  (gram) G = sum_{|P|<=K} P psi psi^dag P, N = sum_{|P|<=K} P psi psi^T P^T, by a dynamic programme over Pauli-weight
         buckets (sum_{s in XYZ} s M s = 2 Tr_j M (x) I - M; block formula for sum s M s^T),
         G_R = 1/2 [[GR+NR, -GI+NI],[GI+NI, GR-NR]] + y y^T (y = embedded i psi); eigenvalues.
Prediction (Lemma B'): if R(K) holds at both factors then rank V_K = 2(D_a + D_b - 1) + dim_R W_K,
  W_K = sum_{j=1}^{K-1} span_R{a (x) b : a in A_j, b in B_{K-j}},  A_j = Pi_perp_a span_R{P psi_a : |P| <= j}.
In the package this script is used for the remark after the proof of Lemma B in the paper:
  python3 numerics/direct_glue_rank.py S_n8_K3_t1001.json S_n4_K2_t1001.json 3,4 gram
(about 2 min; it needed between 3.5 and 6 GB of memory in different runs).
Usage: python3 direct_glue_rank.py <a_cert> <b_cert> <list of K, comma separated> <method: svd|gram|ikisi> [ongoru]
(certificate names are relative to certificates/S/; run from the package root)
"""
import json, sys, itertools, time
import numpy as np

U1 = "certificates/S"
t0 = time.time()


def maske(e):
    a = b = ny = 0
    for j, ch in enumerate(e):
        if ch in "XY":
            a |= 1 << j
        if ch in "ZY":
            b |= 1 << j
        ny += ch == "Y"
    return a, b, ny


def popc(D):
    pc = np.zeros(D, dtype=np.int64)
    for i in range(1, D):
        pc[i] = pc[i >> 1] + (i & 1)
    return pc


def etiketler(n, Kmax, Kmin=0):
    for w in range(Kmin, Kmax + 1):
        for yer in itertools.combinations(range(n), w):
            for h in itertools.product("XYZ", repeat=w):
                e = ["I"] * n
                for j, c in zip(yer, h):
                    e[j] = c
                yield "".join(e), w


def uygula(e, v, pc):
    D = len(v); x = np.arange(D)
    a, b, ny = maske(e)
    out = np.empty(D, dtype=complex)
    out[x ^ a] = (1j) ** ny * (1 - 2 * (pc[b & x] & 1)) * v
    return out


def ust(ad):
    d = json.load(open(f"{U1}/{ad}"))
    n = d["n"]; D = 1 << n; x = np.arange(D); pc = popc(D)
    H = np.zeros((D, D), dtype=complex)
    for e, c in zip(d["etiketler"], d["katsayilar"]):
        a, b, ny = maske(e)
        H[x ^ a, x] += c * (1j) ** ny * (1 - 2 * (pc[b & x] & 1))
    ev, V = np.linalg.eigh(H)
    return n, V[:, -1]


def emb(v):
    return np.concatenate([v.real, v.imag])


def rank_svd(psi, n, K):
    pc = popc(1 << n)
    cols = [emb(uygula(e, psi, pc)) for e, _ in etiketler(n, K, 0)]
    cols.append(emb(1j * psi))
    s = np.linalg.svd(np.array(cols).T, compute_uv=False)
    r = int((s > 1e-9 * s[0]).sum())
    return r, s


def phi_G(M, j, n):
    D = 1 << n; h, l = 1 << (n - 1 - j), 1 << j
    M6 = M.reshape(h, 2, l, h, 2, l)
    T = M6[:, 0, :, :, 0, :] + M6[:, 1, :, :, 1, :]
    out = -M6
    out[:, 0, :, :, 0, :] += 2 * T
    out[:, 1, :, :, 1, :] += 2 * T
    return out.reshape(D, D)


def phi_N(M, j, n):
    D = 1 << n; h, l = 1 << (n - 1 - j), 1 << j
    M6 = M.reshape(h, 2, l, h, 2, l)
    out = M6.copy()
    out[:, 0, :, :, 1, :] = 2 * M6[:, 1, :, :, 0, :] - M6[:, 0, :, :, 1, :]
    out[:, 1, :, :, 0, :] = 2 * M6[:, 0, :, :, 1, :] - M6[:, 1, :, :, 0, :]
    return out.reshape(D, D)


def kova(rho, n, Kmax, phi):
    """B_d = sum_{|S|=d} ((x)_{j in S} phi_j)(rho); returns the cumulative sum_{d<=K} B_d, K = 0..Kmax."""
    B = [rho.copy()] + [np.zeros_like(rho) for _ in range(Kmax)]
    for j in range(n):
        for d in range(Kmax, 0, -1):
            B[d] += phi(B[d - 1], j, n)
    kum = {}
    top = np.zeros_like(rho)
    for d in range(Kmax + 1):
        top = top + B[d]
        kum[d] = top.copy()
    del B
    return kum


def gram_R(G, N, psi):
    GR, GI, NR, NI = G.real, G.imag, N.real, N.imag
    X = 0.5 * np.block([[GR + NR, -GI + NI], [GI + NI, GR - NR]])
    y = emb(1j * psi)
    X += np.outer(y, y)
    return X


def AB_taban(psi, n, j):
    """A real orthonormal basis of A_j (inside psi^perp, as complex vectors)."""
    pc = popc(1 << n)
    vs = []
    for e, _ in etiketler(n, j, 1):
        v = uygula(e, psi, pc)
        vs.append(v - np.vdot(psi, v) * psi)
    if not vs:
        return np.zeros((len(psi), 0), dtype=complex)
    M = np.array([emb(v) for v in vs]).T
    U, s, _ = np.linalg.svd(M, full_matrices=False)
    r = int((s > 1e-9 * s[0]).sum())
    Ub = U[:, :r]
    D = len(psi)
    return Ub[:D] + 1j * Ub[D:]


def ongoru(pa, na, pb, nb, K):
    """Lemma B': R(K) at both factors + the real dimension of W_K (rank of the product vectors)."""
    Da, Db = 1 << na, 1 << nb
    ra, _ = rank_svd(pa, na, K); rb, _ = rank_svd(pb, nb, K)
    vek = []
    for j in range(1, K):
        A = AB_taban(pa, na, j); B = AB_taban(pb, nb, K - j)
        for a in A.T:
            for b in B.T:
                vek.append(emb(np.kron(b, a)))
    if vek:
        s = np.linalg.svd(np.array(vek).T, compute_uv=False)
        w = int((s > 1e-9 * s[0]).sum())
    else:
        w = 0
    return ra == 2 * Da, rb == 2 * Db, w, 2 * (Da + Db - 1) + w


def main():
    a_ad, b_ad = sys.argv[1], sys.argv[2]
    Ks = [int(k) for k in sys.argv[3].split(",")]
    yontem = sys.argv[4]
    ong = len(sys.argv) > 5 and sys.argv[5].startswith("ongoru")
    ong_K = int(sys.argv[5][6:]) if ong and len(sys.argv[5]) > 6 else 99      # "ongoru3": only K <= 3
    na, pa = ust(a_ad); nb, pb = ust(b_ad)
    psi = np.kron(pb, pa)            # psi_a on the low bits (qubits 0..na-1)
    n = na + nb; D = 1 << n
    print(f"== ψ_a = {a_ad} (n={na}) ⊗ ψ_b = {b_ad} (n={nb}) → n = {n}, D = {D}; K = {Ks}; method {yontem}", flush=True)
    if ong:
        for K in [k for k in Ks if k <= ong_K]:
            Ra, Rb, w, r = ongoru(pa, na, pb, nb, K)
            print(f"  [prediction B′] K={K}: R(K) at ψ_a {Ra}, at ψ_b {Rb}; dim_R W_K = {w} (target {2*(Da:=1<<na)*0 + 2*((1<<na)-1)*((1<<nb)-1)}); "
                  f"predicted rank = {r if (Ra and Rb) else 'invalid (R(K) fails at a factor)'} / {2*D}  [{time.time()-t0:.1f} s]",
                  flush=True)
    if yontem in ("svd", "ikisi"):
        for K in Ks:
            r, s = rank_svd(psi, n, K)
            k = min(r, len(s) - 1)
            print(f"  [svd] K={K}: rank_R = {r}/{2*D}; σ_r = {s[r-1]:.4e}, σ_(r+1) = {s[k] if r < len(s) else 0:.3e}"
                  f"  [{time.time()-t0:.1f} s]", flush=True)
    if yontem in ("gram", "ikisi"):
        rho = np.outer(psi, psi.conj())
        G = kova(rho, n, max(Ks), phi_G)
        del rho
        Gs = {K: G[K] for K in Ks}; del G
        rhoT = np.outer(psi, psi)
        N = kova(rhoT, n, max(Ks), phi_N)
        del rhoT
        Ns = {K: N[K] for K in Ks}; del N
        print(f"  [gram] buckets of G and N ready  [{time.time()-t0:.1f} s]", flush=True)
        for K in Ks:
            X = gram_R(Gs[K], Ns[K], psi)
            ev = np.linalg.eigvalsh(X)
            r = int((ev > 1e-10 * ev[-1]).sum())
            alt = ev[-r] if r > 0 else 0.0
            ust_ = ev[-r - 1] if r < len(ev) else 0.0
            print(f"  [gram] K={K}: rank_R = {r}/{2*D}; λ_min(outside the kernel) = {alt:.4e} (σ = {np.sqrt(max(alt,0)):.4e}), "
                  f"next = {ust_:.3e}; λ_max = {ev[-1]:.3e}  [{time.time()-t0:.1f} s]", flush=True)
            del X, ev


if __name__ == "__main__":
    main()
