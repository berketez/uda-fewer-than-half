"""Theorem 2': K*_+(n) <= 1 + max_{m<n} c_gen(m) (qubit-by-qubit gluing + generic C upgrade).
(a) upper bound with the witnessed c_gen (b <= 13; sub-additive closure); (b) conditional upper bound under the
hypothesis c_gen = c_say (labelled "H-C" in the output; NOT proven, NOT used in the paper's theorems);
both are compared with the counting lower bound K_say(n)."""
import sys
sys.path.insert(0, "thresholds")
import dp_glue as u8_dp
N = 128
cg = {}
for b in range(1, N + 1):
    aday = [cg[a] + cg[b - a] for a in range(1, b)] if b > 1 else [1]
    if 2 <= b <= 13:
        aday.append(u8_dp.c_say(b))
    cg[b] = min(aday)
ust_tanik = {n: 1 + max(cg[m] for m in range(1, n)) if n > 1 else 1 for n in range(1, N + 1)}
cs = {n: u8_dp.c_say(n) for n in range(1, N + 1)}
ust_HC = {n: 1 + max(cs[m] for m in range(1, n)) if n > 1 else 1 for n in range(1, N + 1)}
ks = {n: u8_dp.K_say(n) for n in range(1, N + 1)}
print("n | K_say | upper (witnessed) | upper (conditional on H-C)")
for n in list(range(1, 33)) + [40, 48, 56, 64, 80, 96, 112, 128]:
    print(f"{n:3d} | {ks[n]:3d} | {ust_tanik[n]:3d} | {ust_HC[n]:3d}")
print("under H-C, distribution of the difference (upper − K_say), n ≤ 128:", {d: sum(1 for n in range(1, N+1) if ust_HC[n]-ks[n] == d) for d in range(-1, 4)})
print("n ≤ 128 with witnessed upper bound = K_say:", [n for n in range(1, N+1) if ust_tanik[n] == ks[n]])
