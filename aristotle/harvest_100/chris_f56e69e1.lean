/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

open Matrix
open scoped Kronecker MatrixOrder

variable {n m : ℕ}

/-- The Choi matrix of a linear map `Φ` between matrix algebras:
`C = ∑ i j, E i j ⊗ Φ (E i j)`, i.e. `C (i, a) (j, b) = Φ (E i j) a b`. -/
def choiMatrix (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  Matrix.of fun x y => Φ (Matrix.single x.1 y.1 1) x.2 y.2

/-- The ampliation `id_{k} ⊗ Φ` of `Φ`, acting blockwise on `k × k` block matrices. -/
def ampliation (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) (k : ℕ)
    (M : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ) :
    Matrix (Fin k × Fin m) (Fin k × Fin m) ℂ :=
  Matrix.of fun x y => Φ (Matrix.of fun i j => M (x.1, i) (y.1, j)) x.2 y.2

/-- `Φ` is completely positive if every ampliation `id_k ⊗ Φ` maps positive semidefinite
matrices to positive semidefinite matrices. -/
def IsCompletelyPositive (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ (k : ℕ) (M : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ),
    M.PosSemidef → (ampliation Φ k M).PosSemidef

/-- `Φ` admits a Kraus representation. -/
def HasKraus (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∃ A : Fin n × Fin m → Matrix (Fin m) (Fin n) ℂ,
    ∀ X : Matrix (Fin n) (Fin n) ℂ, Φ X = ∑ r, A r * X * (A r)ᴴ

section Aux

variable (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)

/-- Expansion of `Φ X` in the matrix-unit basis. -/
lemma apply_eq_sum_single (X : Matrix (Fin n) (Fin n) ℂ) :
    Φ X = ∑ i, ∑ j, X i j • Φ (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul]
  congr 1
  ext p q
  simp [Matrix.single_apply, Matrix.smul_apply]

/-- The blockwise action of a Kraus family: the ampliation of a map with Kraus operators
`A r` has Kraus operators `1 ⊗ A r`. -/
lemma ampliation_eq_sum_kronecker
    (A : Fin n × Fin m → Matrix (Fin m) (Fin n) ℂ)
    (hA : ∀ X : Matrix (Fin n) (Fin n) ℂ, Φ X = ∑ r, A r * X * (A r)ᴴ)
    (k : ℕ) (M : Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ) :
    ampliation Φ k M
      = ∑ r, ((1 : Matrix (Fin k) (Fin k) ℂ) ⊗ₖ A r) * M
          * (((1 : Matrix (Fin k) (Fin k) ℂ) ⊗ₖ A r))ᴴ := by
  ext x y
  obtain ⟨p, a⟩ := x
  obtain ⟨q, b⟩ := y
  simp only [ampliation, Matrix.of_apply, hA, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ite_mul, one_mul, zero_mul]
  refine Finset.sum_congr rfl fun r₁ _ => Finset.sum_congr rfl fun r₂ _ => ?_
  rw [Finset.sum_eq_single_of_mem q (Finset.mem_univ q)]
  · simp [Finset.sum_ite_eq]
  · intro t _ ht
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [Ne.symm ht]

/-- A map with a Kraus representation is completely positive. -/
lemma isCompletelyPositive_of_hasKraus (h : HasKraus Φ) : IsCompletelyPositive Φ := by
  obtain ⟨A, hA⟩ := h
  intro k M hM
  rw [ampliation_eq_sum_kronecker Φ A hA k M]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun a b ha hb => ha.add hb)
    Matrix.PosSemidef.zero fun r _ => ?_
  exact hM.mul_mul_conjTranspose_same _

/-- If the Choi matrix is positive semidefinite, then `Φ` has a Kraus representation. -/
lemma hasKraus_of_choiMatrix_posSemidef (h : (choiMatrix Φ).PosSemidef) : HasKraus Φ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.nonneg
  refine ⟨fun r => Matrix.of fun a i => star (B r (i, a)), ?_⟩
  intro X
  ext a b
  have hC : ∀ i j, (Φ (Matrix.single i j 1)) a b
      = ∑ r, star (B r (i, a)) * B r (j, b) := by
    intro i j
    have := congrArg (fun M => M (i, a) (j, b)) hB
    simp [choiMatrix, Matrix.mul_apply] at this ⊢
    rw [this]
  have key : ∀ f : Fin n → Fin n → (Fin n × Fin m) → ℂ,
      ∑ i, ∑ j, ∑ r, f i j r = ∑ r, ∑ j, ∑ i, f i j r := fun f =>
    calc ∑ i, ∑ j, ∑ r, f i j r = ∑ i, ∑ r, ∑ j, f i j r :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ r, ∑ i, ∑ j, f i j r := Finset.sum_comm
      _ = ∑ r, ∑ j, ∑ i, f i j r := Finset.sum_congr rfl fun r _ => Finset.sum_comm
  rw [apply_eq_sum_single Φ X]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply, hC, star_star, Finset.sum_mul, Finset.mul_sum]
  refine Eq.trans (key _) ?_
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i _ => by ring

/-- The (unnormalized) maximally entangled state `∑ i j, E i j ⊗ E i j`. -/
def maxEntangled (n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  Matrix.of fun x y => (if x.1 = x.2 then (1 : ℂ) else 0) * (if y.1 = y.2 then 1 else 0)

lemma maxEntangled_posSemidef : (maxEntangled n).PosSemidef := by
  have h : maxEntangled n = (Matrix.of fun (_ : Unit) (x : Fin n × Fin n) =>
      (if x.1 = x.2 then (1 : ℂ) else 0))ᴴ * (Matrix.of fun (_ : Unit) (x : Fin n × Fin n) =>
      (if x.1 = x.2 then (1 : ℂ) else 0)) := by
    ext x y
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, maxEntangled]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma ampliation_maxEntangled : ampliation Φ n (maxEntangled n) = choiMatrix Φ := by
  ext x y
  have hblk : (Matrix.of fun p q => maxEntangled n (x.1, p) (y.1, q))
      = Matrix.single x.1 y.1 (1 : ℂ) := by
    ext p q
    simp [maxEntangled, Matrix.single_apply]
    aesop
  simp only [ampliation, choiMatrix, Matrix.of_apply, hblk]

end Aux
/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
theorem choi_jamiolkowski (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    IsCompletelyPositive Φ ↔ (choiMatrix Φ).PosSemidef := by
  constructor
  · intro h
    have := h n (maxEntangled n) maxEntangled_posSemidef
    rwa [ampliation_maxEntangled] at this
  · intro h
    exact isCompletelyPositive_of_hasKraus Φ (hasKraus_of_choiMatrix_posSemidef Φ h)

/-- The transpose map on `n × n` matrices. -/
def transposeMap (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun := Matrix.transpose
  map_add' _ _ := Matrix.transpose_add _ _
  map_smul' _ _ := Matrix.transpose_smul _ _

/-- Sanity check that complete positivity is a nontrivial condition: the transpose map on
`2 × 2` matrices is positive but not completely positive, since its Choi matrix (the swap
operator) is not positive semidefinite. -/
theorem transposeMap_not_isCompletelyPositive : ¬ IsCompletelyPositive (transposeMap 2) := by
  rw [choi_jamiolkowski]
  intro h
  have h2 := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2
    (fun x => if x = (0, 1) then (1 : ℂ) else if x = (1, 0) then -1 else 0)
  simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_succ, choiMatrix,
    transposeMap, Matrix.single_apply, Matrix.transpose_apply] at h2
  norm_num [Complex.le_def] at h2

end QI

