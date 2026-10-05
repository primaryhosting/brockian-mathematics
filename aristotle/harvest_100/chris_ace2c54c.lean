import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

variable {N M : ℕ}

/-- A linear map between matrix algebras `M_N(ℂ) → M_M(ℂ)`. -/
abbrev MatMap (N M : ℕ) : Type :=
  Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin M) (Fin M) ℂ

/-- The amplification `id_{M_k} ⊗ Φ`, acting on `k × k` block matrices with blocks in
`M_N(ℂ)` by applying `Φ` to each block. -/
def ampl (Φ : MatMap N M) (k : ℕ) (A : Matrix (Fin k × Fin N) (Fin k × Fin N) ℂ) :
    Matrix (Fin k × Fin M) (Fin k × Fin M) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun i j => A (p.1, i) (q.1, j)) p.2 q.2

/-- `Φ` is completely positive when every amplification `id_{M_k} ⊗ Φ` maps positive
semidefinite matrices to positive semidefinite matrices. -/
def IsCompletelyPositive (Φ : MatMap N M) : Prop :=
  ∀ (k : ℕ) (A : Matrix (Fin k × Fin N) (Fin k × Fin N) ℂ),
    A.PosSemidef → (ampl Φ k A).PosSemidef

/-- The Choi matrix of `Φ`, i.e. the block matrix `∑ i, ∑ j, E_{ij} ⊗ Φ (E_{ij})`,
written entrywise as `(i, a), (j, b) ↦ Φ (E_{ij}) a b`. -/
def choiMatrix (Φ : MatMap N M) : Matrix (Fin N × Fin M) (Fin N × Fin M) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single p.1 q.1 1) p.2 q.2

/-- Reversing the order of a triple sum. -/
private lemma sum_rev3 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid δ]
    (f : α → β → γ → δ) : ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  rw [show (∑ b, ∑ a, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c from
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
  exact Finset.sum_comm

/-- Every positive semidefinite matrix factors as `Bᴴ * B`. -/
private lemma posSemidef_factor {n : Type*} [Fintype n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) : ∃ B : Matrix n n ℂ, A = Bᴴ * B := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    (Matrix.nonneg_iff_posSemidef.mpr hA)
  exact ⟨B, by simpa [Matrix.star_eq_conjTranspose] using hB⟩

/-! ### The forward direction -/

/-- The (unnormalised) maximally entangled state `|Ω⟩⟨Ω|` on `ℂ^N ⊗ ℂ^N`, where
`|Ω⟩ = ∑ i, e_i ⊗ e_i`. -/
def omegaMat (N : ℕ) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  Matrix.of fun p q => (if p.1 = p.2 then 1 else 0) * (if q.1 = q.2 then 1 else 0)

lemma omegaMat_posSemidef : (omegaMat N).PosSemidef := by
  have h : omegaMat N
      = (Matrix.of fun (_ : Unit) (p : Fin N × Fin N) =>
          (if p.1 = p.2 then (1 : ℂ) else 0))ᴴ *
        (Matrix.of fun (_ : Unit) (p : Fin N × Fin N) =>
          (if p.1 = p.2 then (1 : ℂ) else 0)) := by
    ext p q
    simp [omegaMat, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma ampl_omegaMat (Φ : MatMap N M) : ampl Φ N (omegaMat N) = choiMatrix Φ := by
  ext p q
  have h : (Matrix.of fun i j => omegaMat N (p.1, i) (q.1, j))
      = Matrix.single p.1 q.1 (1 : ℂ) := by
    ext i j
    simp only [omegaMat, Matrix.of_apply, Matrix.single_apply]
    by_cases h1 : p.1 = i <;> by_cases h2 : q.1 = j <;> simp [h1, h2]
  simp only [ampl, choiMatrix, Matrix.of_apply, h]

/-- Forward direction: a completely positive map has a positive semidefinite Choi matrix. -/
theorem choiMatrix_posSemidef_of_isCompletelyPositive (Φ : MatMap N M)
    (h : IsCompletelyPositive Φ) : (choiMatrix Φ).PosSemidef := by
  have := h N (omegaMat N) omegaMat_posSemidef
  rwa [ampl_omegaMat] at this

/-! ### The reverse direction, via Kraus operators -/

section Kraus

variable (Φ : MatMap N M) (B : Matrix (Fin N × Fin M) (Fin N × Fin M) ℂ)

/-- The Kraus operators read off from a factorisation `choiMatrix Φ = Bᴴ * B`. -/
def kraus (r : Fin N × Fin M) : Matrix (Fin M) (Fin N) ℂ :=
  Matrix.of fun a i => star (B r (i, a))

variable {Φ B}

/-- If `choiMatrix Φ = Bᴴ * B` then `Φ` has the Kraus form `X ↦ ∑ r, V r * X * (V r)ᴴ`. -/
lemma kraus_rep (hB : choiMatrix Φ = Bᴴ * B) (X : Matrix (Fin N) (Fin N) ℂ) :
    Φ X = ∑ r, kraus B r * X * (kraus B r)ᴴ := by
  ext a b
  have hL : Φ X a b = ∑ i, ∑ j, X i j * Φ (Matrix.single i j 1) a b := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) := by
      simp [Matrix.smul_single]
    rw [h, map_smul]
    simp
  have hR : (∑ r, kraus B r * X * (kraus B r)ᴴ) a b
      = ∑ i, ∑ j, X i j * ∑ r, star (B r (i, a)) * B r (j, b) := by
    have e1 : (∑ r, kraus B r * X * (kraus B r)ᴴ) a b
        = ∑ r, ∑ j, ∑ i, X i j * (star (B r (i, a)) * B r (j, b)) := by
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, kraus,
        Matrix.of_apply, star_star, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, sum_rev3]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (Finset.mul_sum ..).symm
  rw [hL, hR]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have h : Φ (Matrix.single i j 1) a b = choiMatrix Φ (i, a) (j, b) := rfl
  rw [h, hB]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The `k`-fold amplification `I_k ⊗ V` of a Kraus operator `V`. -/
def krausAmpl (k : ℕ) (V : Matrix (Fin M) (Fin N) ℂ) :
    Matrix (Fin k × Fin M) (Fin k × Fin N) ℂ :=
  Matrix.of fun p t => if p.1 = t.1 then V p.2 t.2 else 0

lemma krausAmpl_conj_apply {k : ℕ} (V : Matrix (Fin M) (Fin N) ℂ)
    (A : Matrix (Fin k × Fin N) (Fin k × Fin N) ℂ) (p q : Fin k × Fin M) :
    (krausAmpl k V * A * (krausAmpl k V)ᴴ) p q
      = (V * (Matrix.of fun i j => A (p.1, i) (q.1, j)) * Vᴴ) p.2 q.2 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, krausAmpl, Matrix.of_apply,
    Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [apply_ite (star : ℂ → ℂ), star_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun _ _ => ?_
  congr 1
  rw [Finset.sum_comm]
  simp

lemma ampl_eq_sum_conj (hB : choiMatrix Φ = Bᴴ * B) (k : ℕ)
    (A : Matrix (Fin k × Fin N) (Fin k × Fin N) ℂ) :
    ampl Φ k A = ∑ r, krausAmpl k (kraus B r) * A * (krausAmpl k (kraus B r))ᴴ := by
  ext p q
  simp only [ampl, Matrix.of_apply]
  rw [kraus_rep hB]
  simp only [Matrix.sum_apply]
  exact Finset.sum_congr rfl fun r _ => (krausAmpl_conj_apply (kraus B r) A p q).symm

lemma posSemidef_sum_conj (k : ℕ) (A : Matrix (Fin k × Fin N) (Fin k × Fin N) ℂ)
    (hA : A.PosSemidef) (s : Finset (Fin N × Fin M))
    (V : Fin N × Fin M → Matrix (Fin M) (Fin N) ℂ) :
    (∑ r ∈ s, krausAmpl k (V r) * A * (krausAmpl k (V r))ᴴ).PosSemidef := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert r s hr ih =>
      rw [Finset.sum_insert hr]
      refine Matrix.PosSemidef.add ?_ ih
      simpa using hA.conjTranspose_mul_mul_same (krausAmpl k (V r))ᴴ

end Kraus

/-- **Choi–Jamiołkowski isomorphism.**  A linear map `Φ : M_N(ℂ) → M_M(ℂ)` is completely
positive if and only if its Choi matrix `∑ i, ∑ j, E_{ij} ⊗ Φ(E_{ij})` is positive
semidefinite. -/
theorem choi_jamiolkowski (Φ : MatMap N M) :
    IsCompletelyPositive Φ ↔ (choiMatrix Φ).PosSemidef := by
  refine ⟨choiMatrix_posSemidef_of_isCompletelyPositive Φ, fun hC k A hA => ?_⟩
  obtain ⟨B, hB⟩ := posSemidef_factor hC
  rw [ampl_eq_sum_conj hB k A]
  exact posSemidef_sum_conj k A hA Finset.univ _

/-! ### Sanity checks: the notion of complete positivity is non-degenerate -/

lemma choiMatrix_id : choiMatrix (LinearMap.id : MatMap N N) = omegaMat N := by
  ext p q
  simp only [choiMatrix, omegaMat, Matrix.of_apply, LinearMap.id_coe, id_eq,
    Matrix.single_apply]
  by_cases h1 : p.1 = p.2 <;> by_cases h2 : q.1 = q.2 <;> simp [h1, h2]

/-- The identity map is completely positive. -/
theorem isCompletelyPositive_id : IsCompletelyPositive (LinearMap.id : MatMap N N) :=
  (choi_jamiolkowski _).mpr (choiMatrix_id ▸ omegaMat_posSemidef)

/-- The transpose map on `M_2(ℂ)`. -/
noncomputable def transposeMap : MatMap 2 2 :=
  (Matrix.transposeLinearEquiv (Fin 2) (Fin 2) ℂ ℂ).toLinearMap

/-- The transpose map on `M_2(ℂ)` is *not* completely positive: its Choi matrix (the swap
operator) has a negative expectation value. -/
theorem transposeMap_not_isCompletelyPositive : ¬ IsCompletelyPositive transposeMap := by
  intro h
  have hpsd := (choi_jamiolkowski transposeMap).mp h
  set v : Fin 2 × Fin 2 → ℂ :=
    fun p => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0 with hv
  have hval : star v ⬝ᵥ ((choiMatrix transposeMap) *ᵥ v) = -2 := by
    simp only [choiMatrix, transposeMap, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, LinearEquiv.coe_coe, Matrix.transposeLinearEquiv_apply,
      Matrix.of_apply, Pi.star_apply, hv]
    norm_num
  have := hpsd.dotProduct_mulVec_nonneg v
  rw [hval, Complex.le_def] at this
  norm_num at this

end QI

