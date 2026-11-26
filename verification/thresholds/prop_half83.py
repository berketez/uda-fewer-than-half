"""Arithmetic of the proposition "n >= 83" (computer-assisted refinement of the half threshold):
Lemma 1 (C(L) at psi => psi is (2L+1)-UDA) + polynomial genericity (C(L) at one point => Haar-almost everywhere)
+ additivity of C => K*_1(n) <= 2 c(n) + 1, where c(n) is the sub-additive closure of the c_gen(b), b=1..13, given
by the F_p witnesses. c_gen(1)=1 (trivial: span{psi,X psi,Y psi,Z psi}=C^2 generically).
Witnessed values (Table of F_p witnesses): b=2,3: 1; 4-8: 2; 9-13: 3."""
cg = {1: 1, 2: 1, 3: 1, 4: 2, 5: 2, 6: 2, 7: 2, 8: 2, 9: 3, 10: 3, 11: 3, 12: 3, 13: 3}
N = 400
c = [0] * (N + 1)
for n in range(1, N + 1):
    c[n] = min(cg[b] + c[n - b] for b in cg if b <= n)
kotu = [n for n in range(1, N + 1) if not (2 * (2 * c[n] + 1) < n)]
print("largest n with 2c(n)+1 >= n/2 (n<=400):", max(kotu))
print("examples n: K=2c(n)+1, n/2:", [(n, 2 * c[n] + 1, n / 2) for n in (64, 78, 80, 90, 91, 100, 104, 117, 130, 139)])
# 13-periodicity: c(n+13) <= c(n)+3 => K(n+13) <= K(n)+6 < (n+13)/2 if K(n) < n/2 - 0.5 ... tail check
ok = all(2 * (2 * c[n] + 1) < n for n in range(max(kotu) + 1, N + 1))
print("n in (max,400] all have K<n/2:", ok, "; c(n+13) <= c(n)+3 for every 1 <= n <= 387:", all(c[n + 13] <= c[n] + 3 for n in range(1, N - 12)))
