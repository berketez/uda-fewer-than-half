"""Dynamic programming over glued blocks (integers, exact combinatorics; no floating point in the verdicts).

For each n: the Pareto set of triples (KH, r, c) obtainable by gluing exactly certified blocks:
  KH: locality of H; r: real spanning level R(r); c: complex spanning level C(c). S-level = max(KH, r).
Gluing (Lemma B'): (KH,r,c) (x) (KH',r',c') -> (max(KH,KH'), max(r, r', min(r + c', c + r')), c + c').
Generic upgrade (Proposition "generic upgrade"): c <- min(c, c_gen(n)) [and KH <- r if r > KH]; c_gen(n) from
the F_p witnesses.
Variants:
  V0: the plain Lemma B: only (K, c), r = KH = K; blocks = S levels of the S certificates + the C certificates.
  V1: + exact R levels (R(2) at psi_6, R(3) at psi_10).
  V2: V1 + generic C upgrade (c_gen witnesses, sub-additive closure).      <- the variant used in the paper
Output: table for n <= 64; floor(n/2), ceil(kappa_c n), counting lower bound K_say(n) = min{K : M_K(n) >= 2^{n+1} - 2}.
Note: the witnessed values c_gen(b) = c_say(b) for the b given on the command line are INPUTS here; they are
established separately by the F_p witnesses (witnesses/fp_witness.py). The block data of the exact certificates
are likewise inputs, established by the S, C and R verifiers.
Usage: python3 dp_glue.py [b's with c_gen witnesses, comma separated, e.g. 2,3,...,13]
"""
import sys
from math import comb, log2, ceil

NMAX = 64


def M(n, K):
    return sum(comb(n, w) * 3 ** w for w in range(1, K + 1))


def K_say(n):
    K = 0
    while M(n, K) < 2 ** (n + 1) - 2:
        K += 1
    return K


def c_say(n):
    c = 0
    while M(n, c) + 1 < 2 ** n:
        c += 1
    return c


def kappa_c():
    lo, hi = 0.0, 0.75
    f = lambda k: -k * log2(k) - (1 - k) * log2(1 - k) + k * log2(3) - 1
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if f(mid) < 0 else (lo, mid)
    return lo


def pareto(S):
    S = set(S)
    return sorted(t for t in S if not any(u != t and all(a <= b for a, b in zip(u, t)) for u in S))


def yapistir(t1, t2, kip):
    KH1, r1, c1 = t1; KH2, r2, c2 = t2
    if kip == "V0":           # Lemma B (plain form): K = max(K1, K2, min(K1 + c2, c1 + K2)), r = KH = K
        K = max(KH1, KH2, min(KH1 + c2, c1 + KH2))
        return (K, K, c1 + c2)
    r = max(r1, r2, min(r1 + c2, c1 + r2))
    return (max(KH1, KH2), r, c1 + c2)


def calistir(kip, cgen_taniklar):
    bloklar = {1: [(1, 1, 1)], 4: [(2, 2, 2)], 6: [(3, 3, 2)], 8: [(3, 3, 2)], 10: [(4, 4, 3)]}
    if kip in ("V1", "V2"):
        bloklar[6] = [(3, 2, 2)]
        bloklar[10] = [(4, 3, 3)]
    cgen = {}
    if kip == "V2":
        for b in range(1, NMAX + 1):
            aday = [cgen[a] + cgen[b - a] for a in range(1, b)] if b > 1 else []
            if b in cgen_taniklar:
                aday.append(c_say(b))
            if b == 1:
                aday.append(1)
            cgen[b] = min(aday)
    P = {}
    for n in range(1, NMAX + 1):
        S = list(bloklar.get(n, []))
        for n1 in range(1, n // 2 + 1):
            for t1 in P[n1]:
                for t2 in P[n - n1]:
                    S.append(yapistir(t1, t2, kip))
        if kip == "V2":
            S2 = []
            for KH, r, c in S:
                S2.append((max(KH, r), r, min(c, cgen[n])))
            S = S + S2
        P[n] = pareto(S)
    return P, cgen


def main():
    tanik = set(int(b) for b in sys.argv[1].split(",")) if len(sys.argv) > 1 else set()
    kc = kappa_c()
    sonuc = {}
    for kip in ("V0", "V1", "V2"):
        P, cgen = calistir(kip, tanik)
        sonuc[kip] = {n: min(max(KH, r) for KH, r, c in P[n]) for n in P}
        if kip == "V2":
            cg = cgen
            P2 = P
    print(f"κ_c = {kc:.6f}; b with generic C witnesses: {sorted(tanik)}")
    print("c_gen(n) (sub-additive closure), n=1..64:", [cg[n] for n in range(1, NMAX + 1)])
    print(f"{'n':>3} {'⌊n/2⌋':>5} {'K_say':>5} {'⌈κc n⌉':>6} {'V0':>3} {'V1':>3} {'V2':>3}   V2 Pareto (KH,r,c)")
    for n in range(1, NMAX + 1):
        print(f"{n:>3} {n//2:>5} {K_say(n):>5} {ceil(kc*n):>6} {sonuc['V0'][n]:>3} {sonuc['V1'][n]:>3} {sonuc['V2'][n]:>3}   "
              f"{P2[n][:4]}")
    for kip in ("V0", "V1", "V2"):
        alt = [n for n in range(1, NMAX + 1) if sonuc[kip][n] < n / 2]
        tam = [n for n in range(1, NMAX + 1) if sonuc[kip][n] <= n // 2 and n % 2 == 1]
        coz = [n for n in range(1, NMAX + 1) if sonuc[kip][n] <= n // 2]
        N0 = next(N for N in range(NMAX, 0, -1) if sonuc[kip][N] > N // 2) + 1 if any(sonuc[kip][N] > N // 2 for N in range(1, NMAX + 1)) else 1
        N0s = next(N for N in range(NMAX, 0, -1) if not sonuc[kip][N] < N / 2) + 1
        fark = max(sonuc[kip][n] - n / 4 for n in range(1, NMAX + 1))
        fark_son = max(sonuc[kip][n] - n / 4 for n in range(33, NMAX + 1))
        print(f"[{kip}] n with K < n/2: {alt}")
        print(f"[{kip}] n with K ≤ ⌊n/2⌋: {coz}")
        print(f"[{kip}] K ≤ ⌊n/2⌋ for every n ≥ {N0} (n ≤ {NMAX}); K < n/2 for every n ≥ {N0s} in this range")
        print(f"[{kip}] max_n (K − n/4) = {fark:.2f} (n ≤ 64), on n ∈ [33,64] {fark_son:.2f}; "
              f"K/n (n=64) = {sonuc[kip][64]/64:.4f}")


def ek_ozet(tanik):
    """For V2: exact matches (K_say = K_V2), constants of the 13-window, lists for the Jones-Linden discussion."""
    P, cg = calistir("V2", tanik)
    K = {n: min(max(a, r) for a, r, c in P[n]) for n in P}
    esit = [n for n in range(1, NMAX + 1) if K[n] == K_say(n)]
    print(f"[V2] n ≤ 64 with K_say(n) = K_V2(n) (K*_+(n) determined EXACTLY): {esit}")
    print(f"[V2] largest difference K_V2 − K_say (n ≤ 64): {max(K[n] - K_say(n) for n in range(1, NMAX+1))}")
    # 13-block recursion: K(n+13) <= K(n) + 3 (n >= 1) => K(n) <= (3n + C13)/13, C13 = max_{s in window}(13K(s) - 3s)
    b13 = P[13]
    print(f"[V2] n = 13 Pareto: {b13}")
    for bas in (1, 14, 27, 40):
        C = max(13 * K[s] - 3 * s for s in range(bas, bas + 13))
        print(f"[V2] window s ∈ [{bas},{bas+12}]: for every n ≥ {bas}, K*_+(n) ≤ (3n + {C})/13")
    # check: does the recursion actually hold in the table?
    ok = all(K[n + 13] <= K[n] + 3 for n in range(1, NMAX - 12))
    print(f"[V2] in the table K(n+13) ≤ K(n) + 3 for every n ≤ {NMAX-13}: {ok}")


if __name__ == "__main__":
    main()
    ek_ozet(set(int(b) for b in sys.argv[1].split(",")) if len(sys.argv) > 1 else set())
