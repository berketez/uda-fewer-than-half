"""Additional small checks (light; runtime <= 2 min).
 (i) An n=2, K=1 example: lambda_max(Pi H Pi) < a but psi is not an eigenvector; tau has the same 1-body marginals.
 (ii) Distribution of the covering radius of random Lagrangians at small m (how lossy is the stabilizer witness?).
     Part (ii) with m = 8, L = 2 is the computation behind the remark "the route is lossy at finite n" in the paper.
"""
import random
import sys
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from lemma23 import random_lagrangian, syndrome, paulis_upto

# (i)
X = np.array([[0, 1], [1, 0]], complex); Y = np.array([[0, -1j], [1j, 0]]); Z = np.diag([1., -1.]).astype(complex); I = np.eye(2)
psi = np.array([np.sqrt(3) / 2, 0, 0, 0.5], complex)
rho = np.outer(psi, psi.conj())
H = sum(np.real(np.trace(rho @ P)) * P for P in [np.kron(A, I) for A in (X, Y, Z)] + [np.kron(I, A) for A in (X, Y, Z)])
a = np.real(psi.conj() @ H @ psi)
Pi = np.eye(4) - rho
lmax = np.linalg.eigvalsh(Pi @ H @ Pi).max()
Hpsi = H @ psi
par = np.linalg.norm(Hpsi - (psi.conj() @ Hpsi) * psi)
tau = np.diag([0.75, 0, 0, 0.25]).astype(complex)
def marg1(r):
    R = r.reshape(2, 2, 2, 2)
    return np.einsum('ajbj->ab', R), np.einsum('jajb->ab', R)
m_r, m_t = marg1(rho), marg1(tau)
print(f"(i) a = {a:.6f}, lambda_max(Pi H Pi) = {lmax:.6f}, ||(1-psi psi^dag) H psi|| = {par:.6f}, "
      f"difference of 1-body marginals (tau - rho) = {max(np.abs(m_r[0]-m_t[0]).max(), np.abs(m_r[1]-m_t[1]).max()):.1e}, "
      f"tau != rho: {np.abs(tau-rho).max():.3f}")

# (ii)
rng = random.Random(2026)
for (m, L, N) in [(8, 2, 1500), (10, 3, 150)]:
    ball = paulis_upto(m, L)
    best, hist = 0, {}
    for _ in range(N):
        g = random_lagrangian(m, rng)
        c = len({syndrome(p, g) for p in ball})
        best = max(best, c)
        hist[c == 2 ** m] = hist.get(c == 2 ** m, 0) + 1
    print(f"(ii) m={m}, L={L}: b={len(ball)}, number of cosets {2**m}; among {N} random Lagrangians, covering radius <= L: "
          f"{hist.get(True, 0)}; most cosets hit = {best}", flush=True)
