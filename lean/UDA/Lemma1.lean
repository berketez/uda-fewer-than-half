import UDA.Marginal

/-!
# Lemma 1: the spanning condition implies UDA and UGS

If the vectors `pauli p *ᵥ ψ` with `wt p ≤ L` span `ℂ^(2^n)` (condition `SpanC n L ψ`), then

* `ψ` is the unique ground state (with energy zero) of a positive semidefinite
  `(2L+1)`-local Hamiltonian `G` (`IsUGS n (2L+1) ψ`), and
* for a unit vector `ψ`, every density matrix with the same Pauli expectations as `|ψ⟩⟨ψ|`
  up to weight `2L+1` equals `|ψ⟩⟨ψ|` (`IsUDAPauli n (2L+1) ψ`).

Proof outline. Choose Pauli labels `p_i` (`wt p_i ≤ L`) such that the vectors `P_i ψ` form a
basis. For every single-qubit Pauli `Q ∈ {X_j, Z_j}` let `C_Q` be the matrix of `Q` in this
basis and put `A_{Q,i} = Q P_i - ∑_j (C_Q)_{ji} P_j`, so that `A_{Q,i} ψ = 0`. The operator
`G = ∑ A_{Q,i}ᴴ A_{Q,i}` is positive semidefinite and `(2L+1)`-local, because
`(Q P_i)ᴴ (Q P_i) = 1`. If `A_{Q,i} φ = 0` for all `Q, i`, the linear map `T` with
`T (P_i ψ) = P_i φ` commutes with every `X_j` and `Z_j`, hence is a scalar `c`, and `φ = c ψ`.
For the UDA statement, a density matrix `ρ` with the same expectations satisfies
`tr (ρ G) = ⟨ψ, G ψ⟩ = 0`, which forces `A_{Q,i} ρ = 0`; so every column of `ρ` is a multiple
of `ψ`, and hermiticity together with `tr ρ = 1` gives `ρ = |ψ⟩⟨ψ|`.
-/

open Matrix
open scoped ComplexOrder

namespace UDA

namespace L1

variable {n : ℕ}

/-! ### Locality of products and adjoints -/

theorem mul_mem_localOps {K K' : ℕ} {M N : Matrix (Idx n) (Idx n) ℂ}
    (hM : M ∈ localOps n K) (hN : N ∈ localOps n K') : M * N ∈ localOps n (K + K') := by
  unfold localOps at hM hN
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    induction hN using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨q, hq, rfl⟩ := hy
      rw [pauli_mul]
      exact Submodule.smul_mem _ _
        (pauli_mem_localOps (le_trans (wt_add_le p q) (add_le_add hp hq)))
    | zero =>
      rw [Matrix.mul_zero]
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      rw [Matrix.mul_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [Matrix.mul_smul]
      exact Submodule.smul_mem _ c hy
  | zero =>
    rw [Matrix.zero_mul]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [Matrix.add_mul]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [Matrix.smul_mul]
    exact Submodule.smul_mem _ c hx

theorem conjTranspose_mem_localOps {K : ℕ} {M : Matrix (Idx n) (Idx n) ℂ}
    (hM : M ∈ localOps n K) : Mᴴ ∈ localOps n K := by
  unfold localOps at hM
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    rw [pauli_conjTranspose]
    exact Submodule.smul_mem _ _ (pauli_mem_localOps hp)
  | zero =>
    rw [Matrix.conjTranspose_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [Matrix.conjTranspose_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [Matrix.conjTranspose_smul]
    exact Submodule.smul_mem _ _ hx

/-- Expectations of `K`-local operators are determined by the Pauli expectations up to
weight `K`. -/
theorem trace_eq_of_mem_localOps {K : ℕ} {ρ σ : Matrix (Idx n) (Idx n) ℂ}
    (h : ∀ p : PL n, wt p ≤ K → (ρ * pauli p).trace = (σ * pauli p).trace)
    {G : Matrix (Idx n) (Idx n) ℂ} (hG : G ∈ localOps n K) :
    (ρ * G).trace = (σ * G).trace := by
  unfold localOps at hG
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    exact h p hp
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, hx, hy]
  | smul c x _ hx =>
    rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, hx]

/-- `(B - C)ᴴ (B - C)` is `(2L+1)`-local when `B` is an `(L+1)`-local unitary and `C` is
`L`-local: the only product of two `(L+1)`-local factors is `Bᴴ B = 1`. -/
theorem sub_sq_mem {L : ℕ} {B C : Matrix (Idx n) (Idx n) ℂ}
    (hB : B ∈ localOps n (1 + L)) (hC : C ∈ localOps n L) (hBB : Bᴴ * B = 1) :
    (B - C)ᴴ * (B - C) ∈ localOps n (2 * L + 1) := by
  have h1 : Bᴴ * B ∈ localOps n (2 * L + 1) := by
    rw [hBB, ← pauli_zero]
    exact pauli_mem_localOps (by simp)
  have h2 : Bᴴ * C ∈ localOps n (2 * L + 1) :=
    localOps_mono (by omega) (mul_mem_localOps (conjTranspose_mem_localOps hB) hC)
  have h3 : Cᴴ * B ∈ localOps n (2 * L + 1) :=
    localOps_mono (by omega) (mul_mem_localOps (conjTranspose_mem_localOps hC) hB)
  have h4 : Cᴴ * C ∈ localOps n (2 * L + 1) :=
    localOps_mono (by omega) (mul_mem_localOps (conjTranspose_mem_localOps hC) hC)
  rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 h2) (Submodule.sub_mem _ h3 h4)

/-! ### Single-qubit Paulis and the commutant -/

/-- The single-qubit labels: `X_j` for `(false, j)` and `Z_j` for `(true, j)`. -/
def qlab (q : Bool × Fin n) : PL n :=
  if q.1 then (0, Pi.single q.2 1) else (Pi.single q.2 1, 0)

theorem wt_qlab_le (q : Bool × Fin n) : wt (qlab q) ≤ 1 := by
  unfold wt
  calc _ ≤ ({q.2} : Finset (Fin n)).card := by
        apply Finset.card_le_card
        intro l hl
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
        rw [Finset.mem_singleton]
        by_contra hne
        unfold qlab at hl
        split_ifs at hl <;> simp [hne] at hl
    _ = 1 := Finset.card_singleton _

theorem bdot_single_left (j : Fin n) (b : Idx n) : bdot (Pi.single j 1) b = b j := by
  simp [bdot, Pi.single_apply]

theorem sgn_injective {s t : ZMod 2} (h : sgn s = sgn t) : s = t := by
  unfold sgn at h
  split_ifs at h with h1 h2 h2
  · rw [h1, h2]
  · norm_num at h
  · norm_num at h
  · rw [zmod2_eq_one_of_ne_zero h1, zmod2_eq_one_of_ne_zero h2]

theorem mul_pauli_apply (M : Matrix (Idx n) (Idx n) ℂ) (q : PL n) (a b : Idx n) :
    (M * pauli q) a b = M a (b + q.1) * sgn (bdot q.2 b) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (b + q.1)]
  · rw [pauli_apply, ite_eq_left rfl]
  · intro c _ hc
    rw [pauli_apply, ite_eq_right hc, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem pauli_mul_apply (q : PL n) (M : Matrix (Idx n) (Idx n) ℂ) (a b : Idx n) :
    (pauli q * M) a b = sgn (bdot q.2 (a + q.1)) * M (a + q.1) b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (a + q.1)]
  · rw [pauli_apply, ite_eq_left (bits_eq_add_comm.mp rfl)]
  · intro c _ hc
    rw [pauli_apply, ite_eq_right (fun h => hc (bits_eq_add_comm.mpr h)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A function of two bit strings invariant under every simultaneous single-bit flip is
invariant under simultaneous flips of any set of bits. -/
theorem shift_sum (f : Idx n → Idx n → ℂ)
    (hf : ∀ j (a b : Idx n), f (a + Pi.single j 1) (b + Pi.single j 1) = f a b)
    (s : Finset (Fin n)) (a b : Idx n) :
    f (a + ∑ j ∈ s, Pi.single j 1) (b + ∑ j ∈ s, Pi.single j 1) = f a b := by
  induction s using Finset.induction_on generalizing a b with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, ← add_assoc, ← add_assoc, ih, hf]

/-- Every bit string is the sum of the unit vectors of its support. -/
theorem eq_sum_single (x : Idx n) :
    x = ∑ j ∈ Finset.univ.filter (fun j => x j ≠ 0), Pi.single j 1 := by
  funext l
  rw [Finset.sum_apply]
  simp only [Pi.single_apply, Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : x l = 0
  · simp [h]
  · simp [zmod2_eq_one_of_ne_zero h]

/-- A matrix commuting with every `X_j` and every `Z_j` is a multiple of the identity. -/
theorem commutant (M : Matrix (Idx n) (Idx n) ℂ)
    (hX : ∀ j, M * pauli (Pi.single j 1, 0) = pauli (Pi.single j 1, 0) * M)
    (hZ : ∀ j, M * pauli (0, Pi.single j 1) = pauli (0, Pi.single j 1) * M) :
    M = M 0 0 • (1 : Matrix (Idx n) (Idx n) ℂ) := by
  have hoff : ∀ a b : Idx n, a ≠ b → M a b = 0 := by
    intro a b hab
    obtain ⟨j, hj⟩ : ∃ j, a j ≠ b j := by
      by_contra h
      push Not at h
      exact hab (funext h)
    have h0 := congrFun (congrFun (hZ j) a) b
    rw [mul_pauli_apply, pauli_mul_apply] at h0
    simp only [add_zero, bdot_single_left] at h0
    have h2 : M a b * (sgn (b j) - sgn (a j)) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd (sgn_injective (sub_eq_zero.mp h)).symm hj
  have hshift : ∀ j (a b : Idx n), M (a + Pi.single j 1) (b + Pi.single j 1) = M a b := by
    intro j a b
    have h0 := congrFun (congrFun (hX j) a) (b + Pi.single j 1)
    rw [mul_pauli_apply, pauli_mul_apply] at h0
    simp only [bdot_zero_left, sgn_zero, mul_one, one_mul] at h0
    rw [add_assoc b, bits_add_self, add_zero] at h0
    exact h0.symm
  have hdiag : ∀ x : Idx n, M x x = M 0 0 := by
    intro x
    have h0 := shift_sum (fun a b => M a b) hshift (Finset.univ.filter fun j => x j ≠ 0) 0 0
    simp only [zero_add] at h0
    rw [← eq_sum_single x] at h0
    exact h0
  ext a b
  by_cases hab : a = b
  · subst hab
    simp [hdiag]
  · simp [hab, hoff a b hab]

/-! ### The Hamiltonian `G` -/

section Construction

variable {ι : Type} [Fintype ι] (b : Module.Basis ι ℂ (Idx n → ℂ)) (lab : ι → PL n)

/-- Coefficients of `Q (b i)` in the basis `b`, for `Q` a single-qubit Pauli. -/
noncomputable def coef (q : Bool × Fin n) (i j : ι) : ℂ :=
  b.repr (pauli (qlab q) *ᵥ b i) j

/-- The operators `A_{Q,i} = Q P_i - ∑_j (C_Q)_{ji} P_j`. -/
noncomputable def Amat (k : (Bool × Fin n) × ι) : Matrix (Idx n) (Idx n) ℂ :=
  pauli (qlab k.1) * pauli (lab k.2) - ∑ j, coef b k.1 k.2 j • pauli (lab j)

/-- The Hamiltonian `G = ∑_{Q,i} A_{Q,i}ᴴ A_{Q,i}`. -/
noncomputable def Gmat : Matrix (Idx n) (Idx n) ℂ :=
  ∑ k, (Amat b lab k)ᴴ * Amat b lab k

variable {b lab}

theorem Amat_mulVec_psi {ψ : Idx n → ℂ} (hb : ∀ i, b i = pauli (lab i) *ᵥ ψ)
    (k : (Bool × Fin n) × ι) : Amat b lab k *ᵥ ψ = 0 := by
  unfold Amat coef
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← hb, Matrix.sum_mulVec, sub_eq_zero]
  simp only [Matrix.smul_mulVec, ← hb]
  exact (b.sum_repr _).symm

theorem Gmat_mem {L : ℕ} (hlab : ∀ i, wt (lab i) ≤ L) :
    Gmat b lab ∈ localOps n (2 * L + 1) := by
  refine Submodule.sum_mem _ fun k _ => ?_
  unfold Amat
  apply sub_sq_mem
  · exact mul_mem_localOps (pauli_mem_localOps (wt_qlab_le _)) (pauli_mem_localOps (hlab _))
  · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (pauli_mem_localOps (hlab j))
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (pauli (qlab k.1))ᴴ,
      pauli_conjTranspose_mul_self, Matrix.one_mul, pauli_conjTranspose_mul_self]

theorem Gmat_posSemidef : (Gmat b lab).PosSemidef :=
  Matrix.posSemidef_sum _ fun _ _ => Matrix.posSemidef_conjTranspose_mul_self _

theorem Gmat_mulVec_eq_zero_iff (v : Idx n → ℂ) :
    Gmat b lab *ᵥ v = 0 ↔ ∀ k, Amat b lab k *ᵥ v = 0 := by
  constructor
  · intro h k
    have h0 : star v ⬝ᵥ (Gmat b lab *ᵥ v) = 0 := by rw [h, dotProduct_zero]
    unfold Gmat at h0
    rw [Matrix.sum_mulVec, dotProduct_sum] at h0
    have hnn : ∀ k ∈ (Finset.univ : Finset ((Bool × Fin n) × ι)),
        0 ≤ star v ⬝ᵥ (((Amat b lab k)ᴴ * Amat b lab k) *ᵥ v) :=
      fun k _ => (Matrix.posSemidef_conjTranspose_mul_self _).dotProduct_mulVec_nonneg v
    have hk := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 k (Finset.mem_univ _)
    rw [(Matrix.posSemidef_conjTranspose_mul_self _).dotProduct_mulVec_zero_iff] at hk
    exact (Matrix.conjTranspose_mul_self_mulVec_eq_zero _ _).mp hk
  · intro h
    unfold Gmat
    rw [Matrix.sum_mulVec]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Matrix.mulVec_mulVec, h k, Matrix.mulVec_zero]

/-- The kernel of all `A_{Q,i}` is the line through `ψ`. -/
theorem eq_smul_of_Amat {ψ φ : Idx n → ℂ} (hb : ∀ i, b i = pauli (lab i) *ᵥ ψ)
    (h : ∀ k, Amat b lab k *ᵥ φ = 0) : ∃ c : ℂ, φ = c • ψ := by
  obtain ⟨T, hT⟩ : ∃ T : (Idx n → ℂ) →ₗ[ℂ] (Idx n → ℂ), ∀ i, T (b i) = pauli (lab i) *ᵥ φ :=
    ⟨b.constr ℂ fun i => pauli (lab i) *ᵥ φ, fun i => b.constr_basis ℂ _ i⟩
  have hcomm : ∀ q, T ∘ₗ Matrix.toLin' (pauli (qlab q)) =
      Matrix.toLin' (pauli (qlab q)) ∘ₗ T := by
    intro q
    apply b.ext
    intro i
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      hT]
    conv_lhs => rw [← b.sum_repr (pauli (qlab q) *ᵥ b i)]
    rw [map_sum]
    simp only [map_smul, hT]
    have h0 := h (q, i)
    simp only [Amat, coef, Matrix.sub_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec,
      sub_eq_zero, ← Matrix.mulVec_mulVec] at h0
    rw [h0]
  have hM : ∀ q, LinearMap.toMatrix' T * pauli (qlab q) = pauli (qlab q) * LinearMap.toMatrix' T := by
    intro q
    have h0 := congrArg LinearMap.toMatrix' (hcomm q)
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at h0
  have hM1 := commutant (LinearMap.toMatrix' T) (fun j => hM (false, j)) (fun j => hM (true, j))
  have hTv : ∀ v, T v = LinearMap.toMatrix' T 0 0 • v := by
    intro v
    rw [← LinearMap.toMatrix'_mulVec T v]
    conv_lhs => rw [hM1]
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  obtain ⟨i₀⟩ := b.index_nonempty
  refine ⟨LinearMap.toMatrix' T 0 0, ?_⟩
  have h1 : pauli (lab i₀) *ᵥ φ = pauli (lab i₀) *ᵥ (LinearMap.toMatrix' T 0 0 • ψ) := by
    rw [← hT, hTv, hb, Matrix.mulVec_smul]
  have h2 := congrArg (fun v => (pauli (lab i₀))ᴴ *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, pauli_conjTranspose_mul_self, Matrix.one_mulVec] at h2
  exact h2

/-- If `tr (ρ G) = 0` for a positive semidefinite `ρ`, then `A_{Q,i} ρ = 0` for all `Q, i`. -/
theorem Amat_mul_eq_zero {ρ : Matrix (Idx n) (Idx n) ℂ} (hρ : ρ.PosSemidef)
    (htr : (ρ * Gmat b lab).trace = 0) (k : (Bool × Fin n) × ι) : Amat b lab k * ρ = 0 := by
  have hsum : (ρ * Gmat b lab).trace = ∑ k, (Amat b lab k * ρ * (Amat b lab k)ᴴ).trace := by
    unfold Gmat
    rw [Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (ρ * _) _, ← Matrix.mul_assoc]
  have hnn : ∀ k ∈ (Finset.univ : Finset ((Bool × Fin n) × ι)),
      0 ≤ (Amat b lab k * ρ * (Amat b lab k)ᴴ).trace :=
    fun k _ => (hρ.mul_mul_conjTranspose_same _).trace_nonneg
  rw [hsum] at htr
  have hk := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp htr k (Finset.mem_univ _)
  rw [(hρ.mul_mul_conjTranspose_same _).trace_eq_zero_iff] at hk
  have hv : ∀ v, (ρ * (Amat b lab k)ᴴ) *ᵥ v = 0 := by
    intro v
    rw [← Matrix.mulVec_mulVec, ← hρ.dotProduct_mulVec_zero_iff, Matrix.star_mulVec,
      Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hk, Matrix.zero_mulVec, dotProduct_zero]
  have hcol : ρ * (Amat b lab k)ᴴ = 0 :=
    Matrix.ext_of_mulVec_single fun i => by rw [hv, Matrix.zero_mulVec]
  have h0 : (Amat b lab k * ρ)ᴴ = 0 := by
    rw [Matrix.conjTranspose_mul, hρ.isHermitian.eq, hcol]
  exact Matrix.conjTranspose_eq_zero.mp h0

end Construction

/-! ### From the columns of `ρ` to `ρ = |ψ⟩⟨ψ|` -/

theorem trace_proj_mul_eq_zero {ψ : Idx n → ℂ} {G : Matrix (Idx n) (Idx n) ℂ}
    (h : G *ᵥ ψ = 0) : (proj ψ * G).trace = 0 := by
  rw [Matrix.trace_mul_comm, proj, Matrix.mul_vecMulVec, h]
  simp [Matrix.trace]

/-- A Hermitian matrix of unit trace whose columns are all multiples of a unit vector `ψ`
is the projector onto `ψ`. -/
theorem eq_proj_of_cols {ψ : Idx n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) {ρ : Matrix (Idx n) (Idx n) ℂ}
    (hH : ρ.IsHermitian) (htr : ρ.trace = 1) (hcol : ∀ c, ∃ d : ℂ, ∀ a, ρ a c = d * ψ a) :
    ρ = proj ψ := by
  choose d hd using hcol
  have hH' : ∀ a c, ρ a c = star (ρ c a) := fun a c => by
    rw [← Matrix.conjTranspose_apply, hH.eq]
  have hψ' : ∑ a, star (ψ a) * ψ a = 1 := hψ
  set s := ∑ a, star (ψ a) * star (d a) with hs
  have hdc : ∀ c, d c = s * star (ψ c) := by
    intro c
    have h1 : ∀ a, star (ψ a) * (d c * ψ a) = star (ψ a) * (star (d a) * star (ψ c)) := by
      intro a
      rw [← hd c a, hH' a c, hd a c, star_mul']
    have hL : ∑ a, star (ψ a) * (d c * ψ a) = d c := by
      calc ∑ a, star (ψ a) * (d c * ψ a) = d c * ∑ a, star (ψ a) * ψ a := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun a _ => by ring
        _ = d c := by rw [hψ', mul_one]
    have hR : ∑ a, star (ψ a) * (star (d a) * star (ψ c)) = s * star (ψ c) := by
      rw [hs, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [← hL, Finset.sum_congr rfl fun a _ => h1 a, hR]
  have hs1 : s = 1 := by
    have h1 : ρ.trace = s * ∑ a, star (ψ a) * ψ a := by
      simp only [Matrix.trace, Matrix.diag_apply, hd, hdc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [htr, hψ', mul_one] at h1
    exact h1.symm
  ext a c
  rw [hd c a, hdc c, hs1, one_mul, proj, Matrix.vecMulVec_apply, Pi.star_apply, mul_comm]

end L1

/-- **Lemma 1.** The spanning condition `C(L)` implies `(2L+1)`-UDA (in Pauli-expectation
form) and that `ψ` is the unique ground state of a `(2L+1)`-local Hamiltonian. -/
theorem lemma1 {n L : ℕ} {ψ : Idx n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (h : SpanC n L ψ) : IsUDAPauli n (2 * L + 1) ψ ∧ IsUGS n (2 * L + 1) ψ := by
  classical
  -- A basis of the form `pauli (lab i) *ᵥ ψ` with `wt (lab i) ≤ L`.
  obtain ⟨t, hts, hspan, hli⟩ :=
    exists_linearIndependent ℂ {v : Idx n → ℂ | ∃ p : PL n, wt p ≤ L ∧ v = pauli p *ᵥ ψ}
  have hfin : t.Finite := (Set.finite_range fun p : PL n => pauli p *ᵥ ψ).subset
    fun v hv => by
      obtain ⟨p, _, rfl⟩ := hts hv
      exact ⟨p, rfl⟩
  let _ : Fintype t := hfin.fintype
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : t → Idx n → ℂ)) := by
    rw [Subtype.range_coe, hspan]
    exact h.ge
  let b : Module.Basis t ℂ (Idx n → ℂ) := Module.Basis.mk hli htop
  let lab : t → PL n := fun i => Classical.choose (hts i.2)
  have hlab : ∀ i, wt (lab i) ≤ L := fun i => (Classical.choose_spec (hts i.2)).1
  have hb : ∀ i, b i = pauli (lab i) *ᵥ ψ := fun i => by
    rw [Module.Basis.mk_apply]
    exact (Classical.choose_spec (hts i.2)).2
  -- The Hamiltonian and its kernel.
  have hG := L1.Gmat_mem (b := b) hlab
  have hpsd := L1.Gmat_posSemidef (b := b) (lab := lab)
  have hker : ∀ v, L1.Gmat b lab *ᵥ v = 0 ↔ ∃ c : ℂ, v = c • ψ := by
    intro v
    rw [L1.Gmat_mulVec_eq_zero_iff]
    constructor
    · exact L1.eq_smul_of_Amat hb
    · rintro ⟨c, rfl⟩ k
      rw [Matrix.mulVec_smul, L1.Amat_mulVec_psi hb, smul_zero]
  refine ⟨?_, ⟨_, hG, hpsd, hker⟩⟩
  -- The UDA statement.
  intro ρ hρ hexp
  have htr : (ρ * L1.Gmat b lab).trace = 0 := by
    rw [L1.trace_eq_of_mem_localOps hexp hG]
    exact L1.trace_proj_mul_eq_zero ((hker ψ).mpr ⟨1, (one_smul _ _).symm⟩)
  refine L1.eq_proj_of_cols hψ hρ.1.isHermitian hρ.2 fun c => ?_
  obtain ⟨d, hd⟩ := L1.eq_smul_of_Amat (φ := ρ *ᵥ Pi.single c 1) hb fun k => by
    rw [Matrix.mulVec_mulVec, L1.Amat_mul_eq_zero hρ.1 htr k, Matrix.zero_mulVec]
  refine ⟨d, fun a => ?_⟩
  have h0 := congrFun hd a
  simpa [Matrix.mulVec_single_one] using h0

end UDA
