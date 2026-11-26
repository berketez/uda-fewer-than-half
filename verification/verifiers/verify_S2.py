"""Second, independently written verifier for S(n,K) certificates (methods differ from verify_S_v3.py).
- Paulis are built as explicit Kronecker products (Gaussian-integer 2x2 matrices; no bit-mask/phase formula).
- Positive-definiteness proof: if N <= 160, Sylvester's criterion (all leading principal minors > 0) by
  fraction-free Bareiss elimination, entirely in Python integers; no Cholesky, no floating point, no residual.
  If N > 160, a separately written integer residual check: X*2^{2f} - tI*2^{2f} - R R^T, row sums in Python integers.
- The Pauli set is enumerated by filtering all 4^n labels, not by weight-ordered itertools.
Scope: intended for n <= 8 (it builds dense Kronecker products); it is not used for n = 10, 12.
Usage: python3 verify_S2.py certificate.json
"""
import sys, json, itertools
from fractions import Fraction
import numpy as np

T2 = {"I": ((1, 0, 0, 1), (0, 0, 0, 0)), "X": ((0, 1, 1, 0), (0, 0, 0, 0)),
      "Z": ((1, 0, 0, -1), (0, 0, 0, 0)), "Y": ((0, 0, 0, 0), (0, -1, 1, 0))}   # (Re, Im), row-major order


def kron_pauli(et):
    """Label -> (Re, Im) integer matrices; Kronecker order: qubit n-1 leftmost (qubit j = bit j of x)."""
    Pr, Pi = np.array([[1]], dtype=np.int64), np.array([[0]], dtype=np.int64)
    for ch in et:                                   # et[0] = qubit 0 = least significant bit => added on the right
        ar, ai = (np.array(v, dtype=np.int64).reshape(2, 2) for v in T2[ch])
        Pr, Pi = np.kron(ar, Pr) - np.kron(ai, Pi), np.kron(ar, Pi) + np.kron(ai, Pr)
    return Pr, Pi


def bareiss_pd(X):
    """Are all leading principal minors of the symmetric integer X positive (Sylvester)? Exact, Python integers."""
    A = [[int(v) for v in row] for row in X]
    N = len(A)
    onceki = 1
    for k in range(N):
        if A[k][k] <= 0:                            # A[k][k] = (k+1)-th leading principal minor
            return False, k
        for i in range(k + 1, N):
            for j in range(k + 1, N):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // onceki
        onceki = A[k][k]
    return True, N


def artik_pd(X, t, f):
    """2^{2f}(X - tI) = R R^T + E => X >= (t - ||E||_inf/2^{2f}) I. int64 used only while the Python-integer bound < 2^62."""
    N = X.shape[0]
    Y = X - t * np.eye(N, dtype=np.int64)
    R = np.rint(np.linalg.cholesky(Y.astype(float)) * 2.0 ** f).astype(np.int64)
    sinir = max(sum(int(v) ** 2 for v in row) for row in R)          # max squared row norm, exact
    assert sinir < 2 ** 62 and int(np.abs(Y).max()) * 4 ** f < 2 ** 62
    E = Y * (1 << (2 * f)) - R @ R.T                                # partial sums <= sinir < 2^62 => exact
    Einf = max(sum(abs(int(v)) for v in row) for row in E)
    return Fraction((1 << (2 * f)) * t - Einf, 1 << (2 * f))


def main(yol):
    C = json.load(open(yol))
    n, K = C["n"], C["K"]
    D = 2 ** n
    tum = [e for e in ("".join(h) for h in itertools.product("IXYZ", repeat=n))
           if 1 <= sum(c != "I" for c in e) <= K]
    M = len(tum)
    assert set(C["etiketler"]) <= set(tum) and len(set(C["etiketler"])) == len(C["etiketler"])
    HR = np.zeros((D, D), dtype=np.int64); HI = np.zeros((D, D), dtype=np.int64)
    for e, c in zip(C["etiketler"], C["katsayilar"]):
        Pr, Pi = kron_pauli(e)
        HR += c * Pr; HI += c * Pi
    assert (HR == HR.T).all() and (HI == -HI.T).all()
    wr = np.array([u for u, _ in C["w"]], dtype=object); wi = np.array([v for _, v in C["w"]], dtype=object)
    zr = np.array([u for u, _ in C["z"]], dtype=np.int64); zi = np.array([v for _, v in C["z"]], dtype=np.int64)
    Hr_o, Hi_o = HR.astype(object), HI.astype(object)
    hwr = Hr_o.dot(wr) - Hi_o.dot(wi); hwi = Hr_o.dot(wi) + Hi_o.dot(wr)
    pay = int((wr * hwr + wi * hwi).sum()); sanal = int((wr * hwi - wi * hwr).sum())
    payda = int((wr * wr + wi * wi).sum()); Hw2 = int((hwr * hwr + hwi * hwi).sum())
    s = C["s"]
    theta = Fraction(pay, payda)
    print(f"n={n} K={K} M={M}: Kronecker H built; Im(w†Hw) = {sanal}; θ − s = {float(theta - s):.4f} > 0: {theta > s}")
    assert sanal == 0 and theta > s
    p = int((zr * zr + zi * zi).sum()); q = C["q"]
    AR = p * (s * np.eye(D, dtype=np.int64) - HR) + q * (np.outer(zr, zr) + np.outer(zi, zi))
    AI = -p * HI + q * (np.outer(zi, zr) - np.outer(zr, zi))
    Ae = np.block([[AR, -AI], [AI, AR]])
    if Ae.shape[0] <= 160:
        ok, k = bareiss_pd(Ae)
        print(f"  A ≻ 0 (Sylvester/Bareiss, {Ae.shape[0]} leading minors): {ok}")
        assert ok
    else:
        altA = artik_pd(Ae, C["t_A"], C["f_A"])
        print(f"  A ⪰ {float(altA):.4e} I (separately written Python-integer residual): {altA > 0}")
        assert altA > 0
    # B_w: P w with Kronecker Paulis
    wr6, wi6 = wr.astype(np.int64), wi.astype(np.int64)
    wmax = max(abs(int(v)) for v in list(wr) + list(wi))
    assert (M + 2) * wmax ** 2 < 2 ** 62                       # every partial sum of G < 2^62
    sut = [np.concatenate([wr6, wi6]), np.concatenate([-wi6, wr6])]
    for e in tum:
        Pr, Pi = kron_pauli(e)                                 # a single +-1/+-i per row => |Pw| <= wmax
        sut.append(np.concatenate([Pr @ wr6 - Pi @ wi6, Pr @ wi6 + Pi @ wr6]))
    B = np.array(sut, dtype=np.int64).T
    G = B @ B.T                                                # exact (no overflow)
    tau = C["tau"]
    if G.shape[0] <= 160:
        Gs = G - tau * np.eye(2 * D, dtype=np.int64)
        ok, k = bareiss_pd(Gs)
        altG = Fraction(tau) if ok else Fraction(0)
        print(f"  G − τI ≻ 0 (Sylvester/Bareiss, {G.shape[0]} leading minors): {ok}")
        assert ok
    else:
        altG = artik_pd(G, tau, C["f_G"])
        print(f"  G ⪰ {float(altG):.4e} I (separately written Python-integer residual): {altG > 0}")
    r2 = Fraction(Hw2, payda) - theta * theta
    sol = 2 * (M + 2) * r2 / (theta - s) ** 2
    sag = altG / payda
    print(f"  D4: 2(M+2) r̂²/(θ−s)² = {float(sol):.4e} < {float(sag):.4e}: {sol < sag}")
    assert sol < sag
    print(f"SECOND VERIFIER: ALL PASSED (n = {n}, K = {K})")


if __name__ == "__main__":
    main(sys.argv[1])
