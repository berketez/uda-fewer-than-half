"""Second, separately coded check of the modular C(8,2) witness (pure Python lists, no numpy; it shares no code
with fp_witness.py). EXACT (finite-field arithmetic).

v in {0,1}^256, v_j = bit j of the given 256-bit number (j = 0 is the lowest bit).
Matrix [v, Pv (1 <= |P| <= 2)]: entries in Z[i] (0, +-1, +-i). Ring homomorphism Z[i] -> F_p, i -> r (r^2 = -1 mod p).
If the rank over F_p is 256, some 256 x 256 minor is nonzero in F_p, hence nonzero in Z[i] => rank 256 over C
=> span_C{v, Pv} = C^256, i.e. C(8,2) holds at v.
Pauli convention: label[j] acts on qubit j = bit j of the basis index (as in the certificates).
Y = iXZ: Y|0> = i|1>, Y|1> = -i|0>.
"""
import itertools

HEX = "dbd890f0df3d6613ee49a1b9b85313a310b7f09b11e6bb13a0e0677b6d4dcec4"
n, D = 8, 256


def etiketler(n, K):
    for w in range(1, K + 1):
        for yer in itertools.combinations(range(n), w):
            for harfler in itertools.product("XYZ", repeat=w):
                yield dict(zip(yer, harfler))


def uygula(etk, v):
    """P v; entries are pairs of integers (real, imaginary)."""
    out = [(0, 0)] * D
    for x in range(D):
        a, b = v[x]
        if a == 0 and b == 0:
            continue
        y = x
        fr, fi = 1, 0              # phase = fr + i*fi
        for j, h in etk.items():
            bit = (x >> j) & 1
            if h == "X":
                y ^= 1 << j
            elif h == "Z":
                if bit:
                    fr, fi = -fr, -fi
            elif h == "Y":
                y ^= 1 << j
                # Y|0> = i|1>, Y|1> = -i|0>
                c = (0, 1) if bit == 0 else (0, -1)
                fr, fi = fr * c[0] - fi * c[1], fr * c[1] + fi * c[0]
        # (fr + i fi)(a + i b)
        out[y] = (out[y][0] + fr * a - fi * b, out[y][1] + fr * b + fi * a)
    return out


def rank_mod(sutunlar, p, r):
    """Rank over F_p of a list of columns (each a list of D pairs in Z[i]); i -> r."""
    M = [[(re + im * r) % p for (re, im) in col] for col in sutunlar]   # row = column vector (transposed)
    rank, satirlar = 0, [row[:] for row in M]
    m = len(satirlar)
    for c in range(D):
        piv = None
        for i in range(rank, m):
            if satirlar[i][c] % p:
                piv = i
                break
        if piv is None:
            continue
        satirlar[rank], satirlar[piv] = satirlar[piv], satirlar[rank]
        inv = pow(satirlar[rank][c], p - 2, p)
        satirlar[rank] = [(u * inv) % p for u in satirlar[rank]]
        for i in range(m):
            if i != rank and satirlar[i][c]:
                k = satirlar[i][c]
                satirlar[i] = [(u - k * w) % p for u, w in zip(satirlar[i], satirlar[rank])]
        rank += 1
    return rank


def det_mod(sutunlar, p, r):
    A = [[(re + im * r) % p for (re, im) in col] for col in sutunlar]
    A = [list(row) for row in zip(*A)]   # D x D, columns = the given vectors
    N = len(A)
    det = 1
    for c in range(N):
        piv = next((i for i in range(c, N) if A[i][c] % p), None)
        if piv is None:
            return 0
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            det = -det
        det = (det * A[c][c]) % p
        inv = pow(A[c][c], p - 2, p)
        for i in range(c + 1, N):
            if A[i][c]:
                k = (A[i][c] * inv) % p
                A[i] = [(u - k * w) % p for u, w in zip(A[i], A[c])]
    return det % p


if __name__ == "__main__":
    N = int(HEX, 16)
    v = [((N >> j) & 1, 0) for j in range(D)]
    print("‖v‖² =", sum(a for a, _ in v))
    sut = [v] + [uygula(e, v) for e in etiketler(n, 2)]
    print("number of columns:", len(sut))
    for p, r in [(1009, 469), (1013, None), (10009, None)]:
        if r is None:
            r = next(x for x in range(2, p) if (x * x + 1) % p == 0)   # p = 1 (mod 4)
        assert (r * r + 1) % p == 0
        print(f"p = {p}, i ↦ {r}: rank of the full matrix = {rank_mod(sut, p, r)} / {D}")
    print("determinant of the first 256 columns in the witness's column order (mod 1009, i ↦ 469):", det_mod(sut[:256], 1009, 469))
