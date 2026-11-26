"""Check without the S certificates: only the |0> block + Lemma B' + generic upgrade + F_p generic C witnesses (b = 2..13); K(n) and the 13-window constant."""
import sys
sys.path.insert(0, "thresholds")
import dp_glue as u8_dp
N = 64
tanik = set(range(2, 14))
cgen = {}
for b in range(1, N + 1):
    aday = [cgen[a] + cgen[b - a] for a in range(1, b)] if b > 1 else [1]
    if b in tanik:
        aday.append(u8_dp.c_say(b))
    cgen[b] = min(aday)
P = {}
for n in range(1, N + 1):
    S = [(1, 1, 1)] if n == 1 else []
    for n1 in range(1, n // 2 + 1):
        for t1 in P[n1]:
            for t2 in P[n - n1]:
                S.append(u8_dp.yapistir(t1, t2, "V2"))
    S = S + [(max(a, r), r, min(c, cgen[n])) for a, r, c in S]
    P[n] = u8_dp.pareto(S)
K = {n: min(max(a, r) for a, r, c in P[n]) for n in P}
print("K(n) without S certificates, n=1..64:", [K[n] for n in range(1, N + 1)])
print("n=13 Pareto:", P[13])
for bas in (1, 14, 27, 40):
    print(f"window [{bas},{bas+12}]: for every n ≥ {bas}, K*_+(n) ≤ (3n + {max(13*K[s]-3*s for s in range(bas, bas+13))})/13")
print("K(n+13) ≤ K(n)+3 in the table:", all(K[n + 13] <= K[n] + 3 for n in range(1, N - 12)))
