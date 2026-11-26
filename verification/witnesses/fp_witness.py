"""Generic C(b,c) witnesses in finite-field arithmetic (EXACT; no floating point).

Statement. For v in Z[i]^D and P_1..P_D (|P_k| <= c, identity included), det[P_1 v, ..., P_D v] lies in Z[i].
Reduction modulo the prime ideal (p, i - iota) (p = 1 mod 4, iota^2 = -1 mod p) is a ring homomorphism
Z[i] -> F_p. A nonzero image => det != 0 => span_C{Pv : |P| <= c} = C^D. Since det is a (holomorphic) polynomial
in psi, its zero set is a proper algebraic subset of C^D => C(b,c) holds on a Zariski-open, dense, full-measure set.
Rank check: Gaussian elimination over F_p on all M_c + 1 columns (rank = D suffices: a nonzero D x D minor in F_p
=> nonzero in Z[i]).
Usage (command words are kept from the original code; see the README glossary):
  python3 fp_witness.py hakem                    # the C(8,2) witness quoted in the paper: b=8, c=2, p=1009, iota=469
  python3 fp_witness.py rastgele b c seed        # random 0/1 vector witness
  python3 fp_witness.py simetrik b c seed [cift|tek|ikisi]   # Z^{(x)b}-symmetric witness, both parity sectors
  python3 fp_witness.py sektor b c seed cift|tek             # one parity sector of the symmetric witness (b = 13)
"""
import sys, itertools, time
import numpy as np

t0 = time.time()


def sqrt_m1(p):
    for g in range(2, p):
        r = pow(g, (p - 1) // 4, p)
        if r * r % p == p - 1:
            return r
    raise ValueError


def etiketler(n, c, ters=False):
    out = []
    for w in range(0, c + 1):
        for yer in itertools.combinations(range(n), w):
            for h in itertools.product("XYZ", repeat=w):
                e = ["I"] * n
                for j, ch in zip(yer, h):
                    e[j] = ch
                out.append("".join(reversed(e)) if ters else "".join(e))
    return out


def matris_modp(v, n, c, p, iota, ters=False):
    D = 1 << n
    x = np.arange(D)
    pc = np.zeros(D, dtype=np.int64)
    for k in range(1, D):
        pc[k] = pc[k >> 1] + (k & 1)
    ipow = [1, iota, p - 1, (p - iota) % p]
    et = etiketler(n, c, ters)
    A = np.zeros((D, len(et)), dtype=np.int64)
    for k, e in enumerate(et):
        a = b = ny = 0
        for j, ch in enumerate(e):
            if ch in "XY":
                a |= 1 << j
            if ch in "ZY":
                b |= 1 << j
            ny += ch == "Y"
        sgn = 1 - 2 * (pc[b & x] & 1)
        A[x ^ a, k] = (ipow[ny % 4] * sgn * v) % p
    return A % p, et


def rank_det_modp(A, p, kare=False):
    """Rank over F_p (and the determinant if square). Exact: int64, |intermediate| < p^2 < 2^62."""
    assert p * p < (1 << 62)
    A = A.copy() % p
    m, k = A.shape
    r = 0
    det = 1
    for col in range(k):
        if r == m:
            break
        piv = np.nonzero(A[r:, col])[0]
        if len(piv) == 0:
            if kare:
                return r, 0
            continue
        q = r + piv[0]
        if q != r:
            A[[r, q]] = A[[q, r]]
            det = -det
        inv = pow(int(A[r, col]), p - 2, p)
        det = det * int(A[r, col]) % p
        A[r] = A[r] * inv % p
        f = A[r + 1:, col].copy()
        nz = np.nonzero(f)[0]
        if len(nz):
            satirlar = r + 1 + nz
            A[satirlar, col:] = (A[satirlar, col:] - np.outer(f[nz], A[r, col:]) % p) % p
        r += 1
    return r, det % p


def hakem():
    hx = "dbd890f0df3d6613ee49a1b9b85313a310b7f09b11e6bb13a0e0677b6d4dcec4"
    N = int(hx, 16)
    n, c, p = 8, 2, 1009
    iota = 469
    assert iota * iota % p == p - 1, "ι² ≢ −1"
    v = np.array([(N >> x) & 1 for x in range(256)], dtype=np.int64)
    print(f"C(8,2) witness: ‖v‖² = {int(v.sum())} (expected 132); p = {p}, ι = {iota}, ι² ≡ −1 ✓")
    for ters in (False, True):
        A, et = matris_modp(v, n, c, p, iota, ters)
        r, d = rank_det_modp(A[:, :256], p, kare=True)
        rk, _ = rank_det_modp(A, p)
        print(f"  label→bit convention {'reversed (label[j]→bit n−1−j)' if ters else 'direct (label[j]→bit j)'}: "
              f"number of columns {A.shape[1]}, first columns {et[:3]}…; det(first 256) mod {p} = {d}; rank(277 columns) = {rk}/256")
    # second prime
    p2 = 1013; i2 = sqrt_m1(p2)
    A, _ = matris_modp(v, n, c, p2, i2)
    rk, _ = rank_det_modp(A, p2)
    print(f"  second prime p = {p2}, ι = {i2}: rank = {rk}/256  [{time.time()-t0:.1f} s]")


def rastgele(b, c, tohum):
    p = 1000037 if (1000037 % 4 == 1) else 1000033
    while True:
        if p % 4 == 1 and all(p % d for d in range(2, int(p ** 0.5) + 1)):
            break
        p += 1
    iota = sqrt_m1(p)
    rng = np.random.default_rng(tohum)
    v = rng.integers(0, 2, size=1 << b).astype(np.int64)
    A, et = matris_modp(v, b, c, p, iota)
    rk, _ = rank_det_modp(A, p)
    D = 1 << b
    print(f"b={b} c={c} seed={tohum}: v ∈ {{0,1}}^{D} (‖v‖²={int(v.sum())}), p={p}, ι={iota}; columns {A.shape[1]}; "
          f"rank_Fp = {rk}/{D} ⇒ {'C(b,c) GENERIC (witness valid)' if rk == D else 'witness INSUFFICIENT'}  [{time.time()-t0:.1f} s]",
          flush=True)


def simetrik(b, c, tohum, sektor="ikisi"):
    """v supported only on even-parity x (an eigenvector of Z^{(x)b}). Pv stays in the even sector if popcount(a_P)
    is even and in the odd sector if it is odd => span = (span{Pv : a_P even} in the even sector) (+) (span{Pv : a_P odd}
    in the odd sector). rank = rank_even + rank_odd (two separate F_p eliminations). This is only a choice of
    WITNESS; the result is again the statement 'C(b,c) is generic' (a nonzero minor at one point)."""
    p = 1000037
    while not (p % 4 == 1 and all(p % d for d in range(2, int(p ** 0.5) + 1))):
        p += 1
    iota = sqrt_m1(p)
    D = 1 << b
    x = np.arange(D)
    pc = np.zeros(D, dtype=np.int64)
    for k in range(1, D):
        pc[k] = pc[k >> 1] + (k & 1)
    rng = np.random.default_rng(tohum)
    v = rng.integers(0, 2, size=D).astype(np.int64) * (1 - (pc & 1))      # odd-parity entries set to 0
    A, et = matris_modp(v, b, c, p, iota)
    acift = []
    for e in et:
        acift.append(sum(ch in "XY" for ch in e) % 2 == 0)
    acift = np.array(acift)
    cift_x = np.nonzero((pc & 1) == 0)[0]
    tek_x = np.nonzero((pc & 1) == 1)[0]
    # consistency: columns with even a_P vanish on the odd sector, columns with odd a_P vanish on the even sector
    assert not A[np.ix_(tek_x, np.nonzero(acift)[0])].any() and not A[np.ix_(cift_x, np.nonzero(~acift)[0])].any()
    A1 = A[np.ix_(cift_x, np.nonzero(acift)[0])]
    A2 = A[np.ix_(tek_x, np.nonzero(~acift)[0])]
    del A
    print(f"b={b} c={c} seed={tohum} [Z^b-symmetric witness]: sector size {D//2}; columns even {A1.shape[1]}, odd {A2.shape[1]}; "
          f"p={p}", flush=True)
    r1 = r2 = None
    if sektor in ("ikisi", "cift"):
        del_ = A2 if sektor == "cift" else None
        r1, _ = rank_det_modp(A1, p)
        print(f"  even sector rank_Fp = {r1}/{D//2}  [{time.time()-t0:.1f} s]", flush=True)
    if sektor in ("ikisi", "tek"):
        r2, _ = rank_det_modp(A2, p)
        print(f"  odd sector rank_Fp = {r2}/{D//2}  [{time.time()-t0:.1f} s]", flush=True)
    if r1 is not None and r2 is not None:
        print(f"  total rank = {r1 + r2}/{D} ⇒ {'C(b,c) GENERIC (witness valid)' if r1 + r2 == D else 'witness INSUFFICIENT'}", flush=True)


def rank_modp_parcali(A, p, parca=512):
    """The same elimination as rank_det_modp, with in-place updates in row chunks (memory: chunk x columns)."""
    assert p * p < (1 << 62)
    m, k = A.shape
    r = 0
    for col in range(k):
        if r == m:
            break
        piv = np.nonzero(A[r:, col])[0]
        if len(piv) == 0:
            continue
        q = r + piv[0]
        if q != r:
            A[[r, q]] = A[[q, r]]
        inv = pow(int(A[r, col]), p - 2, p)
        A[r, col:] = A[r, col:] * inv % p
        prow = A[r, col:]
        nz = np.nonzero(A[r + 1:, col])[0] + r + 1
        for s0 in range(0, len(nz), parca):
            sat = nz[s0:s0 + parca]
            sub = A[sat, col:]
            sub -= np.outer(sub[:, 0], prow) % p
            sub %= p
            A[sat, col:] = sub
        r += 1
    return r


def sektor_hizli(b, c, tohum, hangi):
    """The same witness as simetrik() (same seed => same v), but builds the matrix of one sector directly."""
    p = 1000037
    while not (p % 4 == 1 and all(p % d for d in range(2, int(p ** 0.5) + 1))):
        p += 1
    iota = sqrt_m1(p)
    D = 1 << b
    x = np.arange(D)
    pc = np.zeros(D, dtype=np.int64)
    for k in range(1, D):
        pc[k] = pc[k >> 1] + (k & 1)
    rng = np.random.default_rng(tohum)
    v = rng.integers(0, 2, size=D).astype(np.int64) * (1 - (pc & 1))
    par = 0 if hangi == "cift" else 1
    satirlar = np.nonzero((pc & 1) == par)[0]
    yer = -np.ones(D, dtype=np.int64); yer[satirlar] = np.arange(len(satirlar))
    ipow = [1, iota, p - 1, (p - iota) % p]
    et = [e for e in etiketler(b, c) if sum(ch in "XY" for ch in e) % 2 == par]
    A = np.zeros((len(satirlar), len(et)), dtype=np.int64)
    kaynak = np.nonzero((pc & 1) == 0)[0]            # support of v (even x)
    for k, e in enumerate(et):
        a = bb = ny = 0
        for j, ch in enumerate(e):
            if ch in "XY":
                a |= 1 << j
            if ch in "ZY":
                bb |= 1 << j
            ny += ch == "Y"
        sgn = 1 - 2 * (pc[bb & kaynak] & 1)
        hedef = yer[kaynak ^ a]
        assert (hedef >= 0).all()
        A[hedef, k] = (ipow[ny % 4] * sgn * v[kaynak]) % p
    print(f"b={b} c={c} seed={tohum} sector={hangi}: {A.shape[0]} rows × {A.shape[1]} columns, p={p}  [{time.time()-t0:.1f} s]",
          flush=True)
    r = rank_modp_parcali(A, p)
    print(f"  {hangi} sector rank_Fp = {r}/{A.shape[0]}  [{time.time()-t0:.1f} s]", flush=True)


if __name__ == "__main__":
    if sys.argv[1] == "sektor":
        sektor_hizli(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5])
    elif sys.argv[1] == "hakem":
        hakem()
    elif sys.argv[1] == "simetrik":
        simetrik(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5] if len(sys.argv) > 5 else "ikisi")
    else:
        rastgele(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
