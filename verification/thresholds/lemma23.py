"""Independent numerical / exact checks of Lemma 2 and Lemma 3 (stabilizer covering and spanning).

Notation: an m-qubit Pauli (phase dropped) = (x, z) bit masks; weight = popcount(x|z);
symplectic product w(p,q) = popcount(x1&z2 ^ z1&x2) mod 2.

Parts
 A) Lagrangian count: for m = 2, 3, 4 ALL Lagrangian subspaces are enumerated; Pr[u in S] = 1/(d+1),
    E N = b/d, Var N = b(d^2-b)/(d^2(d+1)) (exact fractions), Pr[N=0] <= d/b.          [exact; used by run_all.sh]
 B) Lemma 2: uniformly random Lagrangian S, m = 6..10; covering radius R (syndrome method) compared with
    rank V_r psi_S (numerical Gram matrix), r = R-1, R. Also rank = number of cosets hit.     [floating point; optional]
 C) Construction of Lemma 3: S + greedy v's -> W; W^perp in S in W; form rank 2s; F; graph S~;
    is S~ Lagrangian; covering radius <= L + s; does V_{L+s} psi_{S~} span.                  [optional, ~3 min]
This module also provides the helper functions used by lagrangian_cover.py.
Usage: python3 lemma23.py [A|B|C|ABC]
"""
import itertools
import random
import sys
from fractions import Fraction

import numpy as np


def popc(a):
    return bin(a).count("1")


def omega(p, q):
    return popc((p[0] & q[1]) ^ (p[1] & q[0])) & 1


def wt(p):
    return popc(p[0] | p[1])


def add(p, q):
    return (p[0] ^ q[0], p[1] ^ q[1])


def paulis_upto(m, r):
    """All (x,z) of weight <= r."""
    return list(paulis_iter(m, r))


def paulis_iter(m, r):
    yield (0, 0)
    for w in range(1, r + 1):
        for yer in itertools.combinations(range(m), w):
            for harf in itertools.product((1, 2, 3), repeat=w):  # 1=X, 2=Z, 3=Y
                x = z = 0
                for j, h in zip(yer, harf):
                    if h & 1:
                        x |= 1 << j
                    if h & 2:
                        z |= 1 << j
                yield (x, z)


def span_set(vecs):
    s = {(0, 0)}
    for v in vecs:
        s |= {add(a, v) for a in s}
    return s


def random_lagrangian(m, rng):
    """Uniformly random Lagrangian: sequential choice (u_k in span^perp \\ span), Sp-invariant."""
    gens = []
    sp = {(0, 0)}
    while len(gens) < m:
        v = (rng.getrandbits(m), rng.getrandbits(m))
        if v in sp:
            continue
        if any(omega(v, g) for g in gens):
            continue
        gens.append(v)
        sp |= {add(a, v) for a in sp}
    return gens


def syndrome(p, gens):
    s = 0
    for i, g in enumerate(gens):
        if omega(p, g):
            s |= 1 << i
    return s


def covering_radius(m, gens, rmax=None):
    """Syndrome method: since S^perp = S, cosets <-> syndromes. Returns R and r -> number of cosets hit."""
    if rmax is None:
        rmax = m
    hit = set()
    counts = {}
    for w in range(0, rmax + 1):
        if w == 0:
            hit.add(0)
        else:
            for yer in itertools.combinations(range(m), w):
                for harf in itertools.product((1, 2, 3), repeat=w):
                    x = z = 0
                    for j, h in zip(yer, harf):
                        if h & 1:
                            x |= 1 << j
                        if h & 2:
                            z |= 1 << j
                    hit.add(syndrome((x, z), gens))
        counts[w] = len(hit)
        if len(hit) == 2 ** m:
            return w, counts
    return None, counts


# ---------- state vectors ----------

def parity_table(m):
    b = np.arange(2 ** m, dtype=np.int64)
    par = np.zeros((2 ** m,), dtype=np.int64)
    # popcount table
    pc = np.zeros(2 ** m, dtype=np.int64)
    for k in range(m):
        pc += (b >> k) & 1
    return pc


def apply_pauli(p, psi, m, pc):
    """(X^x Z^z psi)[b] = (-1)^{popcount(z & (b^x))} psi[b^x]."""
    x, z = p
    b = np.arange(2 ** m, dtype=np.int64)
    src = b ^ x
    sgn = 1 - 2 * (pc[z & src] & 1)
    return sgn * psi[src]


def stabilizer_state(m, gens, rng_np):
    """Projection: psi proportional to prod_i (I + i^{x.z} X^x Z^z)/2 |random>."""
    pc = parity_table(m)
    D = 2 ** m
    for _ in range(20):
        v = rng_np.normal(size=D) + 1j * rng_np.normal(size=D)
        for g in gens:
            ph = (1j) ** (popc(g[0] & g[1]) % 4)  # Hermitian Pauli
            v = 0.5 * (v + ph * apply_pauli(g, v, m, pc))
        nv = np.linalg.norm(v)
        if nv > 1e-6:
            return v / nv
    raise RuntimeError("projection is zero")


def check_stabilized(m, gens, psi):
    pc = parity_table(m)
    worst = 0.0
    for g in gens:
        ph = (1j) ** (popc(g[0] & g[1]) % 4)
        worst = max(worst, np.linalg.norm(ph * apply_pauli(g, psi, m, pc) - psi))
    return worst


def span_rank(m, psi, r, tol=1e-8):
    """rank [P psi : wt(P) <= r] -- via the Gram matrix M M^dag."""
    pc = parity_table(m)
    D = 2 ** m
    Gm = np.zeros((D, D), dtype=complex)
    batch = []
    for p in paulis_upto(m, r):
        batch.append(apply_pauli(p, psi, m, pc))
        if len(batch) == 512:
            M = np.array(batch).T
            Gm += M @ M.conj().T
            batch = []
    if batch:
        M = np.array(batch).T
        Gm += M @ M.conj().T
    ev = np.linalg.eigvalsh(Gm)
    return int(np.sum(ev > tol * ev[-1])), ev


# ---------- A) exact count ----------

def all_lagrangians(m):
    """All Lagrangian subspaces (as frozensets of elements)."""
    V = [(x, z) for x in range(2 ** m) for z in range(2 ** m)]
    res = set()

    def rec(gens, sp):
        if len(gens) == m:
            res.add(frozenset(sp))
            return
        for v in V:
            if v in sp:
                continue
            if any(omega(v, g) for g in gens):
                continue
            # non-canonical ordered generation; duplicates are removed by the set. No pruning;
            # fast for m <= 3. Separate route for m = 4.
            rec(gens + [v], sp | {add(a, v) for a in sp})

    if m <= 3:
        rec([], {(0, 0)})
        return res
    # m = 4: instead of Sp orbits, grow isotropic subspaces dimension by dimension (a set at every step)
    level = {frozenset({(0, 0)})}
    for k in range(m):
        new = set()
        for sp in level:
            sp_list = list(sp)
            for v in V:
                if v in sp:
                    continue
                if any(omega(v, a) for a in sp_list):
                    continue
                new.add(frozenset(sp | {add(a, v) for a in sp}))
        level = new
    return level


def part_A():
    print("=== A) Exact count of Lagrangian subspaces ===")
    for m in (2, 3, 4):
        Ls = all_lagrangians(m)
        prod = 1
        for i in range(1, m + 1):
            prod *= 2 ** i + 1
        d = 2 ** m
        V = [(x, z) for x in range(d) for z in range(d)]
        # Pr[u in S] for every u != 0
        cnt = {u: 0 for u in V}
        for S in Ls:
            for u in S:
                cnt[u] += 1
        prs = {Fraction(cnt[u], len(Ls)) for u in V if u != (0, 0)}
        print(f"m={m}: number of Lagrangians = {len(Ls)} (formula prod(2^i+1) = {prod}); set of Pr[u in S] = {prs}, 1/(d+1) = {Fraction(1, d+1)}")
        for L in (range(0, m + 1) if m <= 3 else (1, 2, 3)):
            ball = [p for p in V if wt(p) <= L]
            b = len(ball)
            ballset = set(ball)
            EN = Fraction(0)
            EN2 = Fraction(0)
            P0 = Fraction(0)
            tot = len(Ls) * len(V)
            for S in Ls:
                for v in V:
                    N = sum(1 for s in S if add(s, v) in ballset)
                    EN += N
                    EN2 += N * N
                    if N == 0:
                        P0 += 1
            EN /= tot
            EN2 /= tot
            P0 /= tot
            Var = EN2 - EN ** 2
            Var_f = Fraction(b * (d * d - b), d * d * (d + 1))
            cheb = Fraction(d * d - b, b * (d + 1))
            print(f"   L={L}: b={b}  E N = {EN} (b/d = {Fraction(b, d)})  Var N = {Var} (formula {Var_f})  "
                  f"Pr[N=0] = {P0} <= Chebyshev {cheb} <= d/b = {Fraction(d, b)} : "
                  f"{'OK' if (EN == Fraction(b, d) and Var == Var_f and P0 <= cheb <= Fraction(d, b)) else 'ERROR'}")


# ---------- B) Lemma 2 ----------

def part_B(seed=7):
    print("=== B) Lemma 2: covering radius (syndromes) <-> rank V_r psi_S (numerical) ===")
    rng = random.Random(seed)
    rng_np = np.random.default_rng(seed)
    for m in (6, 7, 8, 9, 10):
        for rep in range(2 if m <= 9 else 1):
            gens = random_lagrangian(m, rng)
            # Lagrangian check
            iso = all(omega(a, b) == 0 for a in gens for b in gens)
            dim_ok = len(span_set(gens)) == 2 ** m
            R, counts = covering_radius(m, gens)
            psi = stabilizer_state(m, gens, rng_np)
            stab_err = check_stabilized(m, gens, psi)
            line = f"m={m} #{rep}: isotropic={iso}, dimension={'m' if dim_ok else 'ERROR'}, R={R}, stab. error={stab_err:.1e};"
            for r in sorted(set([max(R - 1, 0), R])):
                rk, ev = span_rank(m, psi, r)
                # are the Gram eigenvalues close to integers (number of Paulis per coset)?
                pos = ev[ev > 1e-8 * ev[-1]]
                intdev = float(np.max(np.abs(pos - np.round(pos)))) if len(pos) else 0.0
                line += f" r={r}: rank={rk}, cosets hit={counts[r]}, D={2**m}, deviation of Gram eigenvalues from integers={intdev:.1e};"
            print(line, flush=True)


# ---------- C) construction of Lemma 3 ----------

def gauss_rank(vecs, nbits):
    """Rank over F2; a vector = one int (x | z << nbits)."""
    rows = [v for v in vecs]
    rank = 0
    piv_rows = []
    for v in rows:
        for pr in piv_rows:
            v = min(v, v ^ pr)
        if v:
            piv_rows.append(v)
            rank += 1
    return rank


def to_int(p, m):
    return p[0] | (p[1] << m)


def part_C(seed=11):
    print("=== C) Construction of Lemma 3: S + greedy v -> W -> graph S~ ===")
    rng = random.Random(seed)
    rng_np = np.random.default_rng(seed)
    for (m, L) in [(6, 1), (7, 1), (8, 2), (9, 2), (10, 2)]:
        gens = random_lagrangian(m, rng)
        d = 2 ** m
        ball = paulis_upto(m, L)
        b = len(ball)
        covered = {syndrome(p, gens) for p in ball}
        U = set(range(d)) - covered
        eps0 = len(U) / d
        # greedy: choose a in syndrome space, U <- U intersected with (U + a)
        chosen = []
        eps_hist = [eps0]
        while U:
            best = None
            for a in range(1, d):
                newU = {u for u in U if (u ^ a) in U}
                if best is None or len(newU) < len(best[1]):
                    best = (a, newU)
            a, U = best
            chosen.append(a)
            eps_hist.append(len(U) / d)
        # for each syndrome a find a v in V (preimage of smallest weight)
        pre = {}
        for p in paulis_iter(m, m):
            s = syndrome(p, gens)
            if s not in pre:
                pre[s] = p
            if len(pre) == d:
                break
        vs = [pre[a] for a in chosen]
        Wgens = gens + vs
        Wset = span_set(Wgens)
        s_dim = len(vs)
        dimW = (len(Wset)).bit_length() - 1
        # covering radius of W <= L ?  (is every point of V in W + B_L)
        V = [(x, z) for x in range(d) for z in range(d)]
        WB = set()
        for w in Wset:
            for p in ball:
                WB.add(add(w, p))
        W_covers = len(WB) == d * d
        # W^perp
        Wperp = [v for v in V if all(omega(v, g) == 0 for g in Wgens)]
        Sset = span_set(gens)
        perp_in_S = all(v in Sset for v in Wperp)
        S_in_W = Sset <= Wset
        # symplectic Gram-Schmidt on W
        basis = list(Wgens)
        pairs = []
        rest = basis[:]
        changed = True
        while True:
            found = None
            for i in range(len(rest)):
                for j in range(i + 1, len(rest)):
                    if omega(rest[i], rest[j]):
                        found = (i, j)
                        break
                if found:
                    break
            if not found:
                break
            i, j = found
            e, f_ = rest[i], rest[j]
            others = [rest[k] for k in range(len(rest)) if k not in (i, j)]
            new_others = []
            for u in others:
                u2 = u
                if omega(u, f_):
                    u2 = add(u2, e)
                if omega(u, e):
                    u2 = add(u2, f_)
                new_others.append(u2)
            pairs.append((e, f_))
            rest = new_others
        radical = rest  # mutually orthogonal
        s2 = len(pairs)
        # graph: m + s2 qubits; new qubit k: e_k -> X_{m+k}, f_k -> Z_{m+k}, radical -> 0
        mt = m + s2
        Sg = []
        for k, (e, f_) in enumerate(pairs):
            Sg.append((e[0] | (1 << (m + k)), e[1]))
            Sg.append((f_[0], f_[1] | (1 << (m + k))))
        for r_ in radical:
            Sg.append(r_)
        iso = all(omega(a, c) == 0 for a in Sg for c in Sg)
        rank = gauss_rank([to_int(p, mt) for p in Sg], mt)
        R, counts = covering_radius(mt, Sg) if rank == mt else (None, {})
        line = (f"m={m}, L={L}: b={b}, d/b={d/b:.3f}, eps0={eps0:.4f} (Chebyshev average bound d/b); greedy eps: "
                f"{[round(x, 5) for x in eps_hist]} (eps_(i+1) <= eps_i^2 ? "
                f"{all(eps_hist[i+1] <= eps_hist[i]**2 + 1e-12 for i in range(len(eps_hist)-1))}); "
                f"t={len(vs)}, dim W={dimW} (m+t={m+len(vs)}); covering radius of W <= L: {W_covers}; "
                f"W^perp ⊂ S: {perp_in_S}; S ⊂ W: {S_in_W}; form rank 2s = {2*s2} (2(dimW-m) = {2*(dimW-m)}); "
                f"radical dimension {len(radical)} (= m - s = {m - s2}); S~: isotropic={iso}, rank={rank} (= m+s = {mt}); "
                f"covering radius of S~ R={R} <= L+s = {L + s2}: {R is not None and R <= L + s2}")
        print(line, flush=True)
        if mt <= 11 and R is not None:
            psi = stabilizer_state(mt, Sg, rng_np)
            rk, _ = span_rank(mt, psi, L + s2)
            print(f"   rank of V_(L+s) psi_S~ = {rk} / {2**mt}  (spanning by Lemma 2: {rk == 2**mt})", flush=True)


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "ABC"
    if "A" in which:
        part_A()
    if "B" in which:
        part_B()
    if "C" in which:
        part_C()
