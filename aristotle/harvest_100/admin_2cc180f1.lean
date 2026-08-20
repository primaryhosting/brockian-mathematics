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

open Matrix
open scoped ComplexOrder

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ` between matrix algebras:
`C (i,a) (j,b) = (Φ Eᵢⱼ) a b`, where `Eᵢⱼ` is the matrix unit. -/
def choiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Matrix (n × m) (n × m) ℂ :=
  Matrix.of fun x y => Φ (Matrix.single x.1 y.1 (1 : ℂ)) x.2 y.2

/-- `Φ` admits a Kraus (operator-sum) representation `Φ X = ∑ k, Kₖ X Kₖᴴ`. -/
def HasKraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∃ (r : ℕ) (K : Fin r → Matrix m n ℂ), ∀ X, Φ X = ∑ k, K k * X * (K k)ᴴ

/-- The amplification `id_κ ⊗ Φ`, acting on `κ`-indexed block matrices. -/
def amplify (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (κ : Type) [Fintype κ]
    (X : Matrix (κ × n) (κ × n) ℂ) : Matrix (κ × m) (κ × m) ℂ :=
  Matrix.of fun x y => Φ (Matrix.of fun i j => X (x.1, i) (y.1, j)) x.2 y.2

/-- Complete positivity: every amplification `id_κ ⊗ Φ` maps positive semidefinite matrices
to positive semidefinite matrices. -/
def IsCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ (κ : Type) [Fintype κ] (X : Matrix (κ × n) (κ × n) ℂ),
    X.PosSemidef → (amplify Φ κ X).PosSemidef

/-- The amplification `1 ⊗ K` of a Kraus operator `K`. -/
def krausAmp (κ : Type) [DecidableEq κ] (K : Matrix m n ℂ) : Matrix (κ × m) (κ × n) ℂ :=
  Matrix.of fun x y => if x.1 = y.1 then K x.2 y.2 else 0

/-- The (unnormalised) maximally entangled state `|ω⟩⟨ω|` with `|ω⟩ = ∑ i, eᵢ ⊗ eᵢ`. -/
def maxEnt (n : Type) [Fintype n] [DecidableEq n] : Matrix (n × n) (n × n) ℂ :=
  Matrix.of fun x y => if x.1 = x.2 ∧ y.1 = y.2 then 1 else 0

omit [Fintype m] [DecidableEq m] in
/-- **Key lemma**: a linear map between matrix algebras is completely determined by its
Choi matrix, via `Φ X a b = ∑ i j, X i j * C (i,a) (j,b)`. -/
theorem apply_eq_sum_choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (X : Matrix n n ℂ)
    (a b : m) : Φ X a b = ∑ i, ∑ j, X i j * choiMatrix Φ (i, a) (j, b) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) := by
    ext a' b'; simp [Matrix.single_apply]
  rw [h, map_smul]
  simp [choiMatrix]

omit [DecidableEq m] in
/-- A positive semidefinite Choi matrix yields a Kraus representation, obtained by
factoring `C = Bᴴ B`. -/
theorem hasKraus_of_choi_posSemidef (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : (choiMatrix Φ).PosSemidef) : HasKraus Φ := by
  classical
  obtain ⟨B, hB⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp h
  set e := (Fintype.equivFin (n × m)).symm with he
  refine ⟨Fintype.card (n × m), fun k => Matrix.of fun a i => star (B (e k) (i, a)), ?_⟩
  intro X
  ext a b
  rw [apply_eq_sum_choi Φ X a b]
  have hC : ∀ i j, choiMatrix Φ (i, a) (j, b) = ∑ p : n × m, star (B p (i, a)) * B p (j, b) := by
    intro i j
    rw [hB]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [hC, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, star_star, Finset.mul_sum, Finset.sum_mul]
  rw [Equiv.sum_comp e (fun p => ∑ j, ∑ i, star (B p (i, a)) * X i j * B p (j, b))]
  simp only [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ⟨fun t => (t.2.2, t.2.1, t.1), fun s => (s.2.2, s.2.1, s.1),
    fun _ => rfl, fun _ => rfl⟩ _ _ (fun t => by simp only [Equiv.coe_fn_mk]; ring)

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem krausAmp_mul_apply {κ : Type} [Fintype κ] [DecidableEq κ] (K : Matrix m n ℂ)
    (X : Matrix (κ × n) (κ × n) ℂ) (x : κ × m) (w : κ × n) :
    (krausAmp κ K * X) x w = ∑ i, K x.2 i * X (x.1, i) w := by
  simp only [Matrix.mul_apply, krausAmp, Matrix.of_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem mul_krausAmp_conjTranspose_apply {κ : Type} [Fintype κ] [DecidableEq κ]
    (K : Matrix m n ℂ) (Y : Matrix (κ × m) (κ × n) ℂ) (x y : κ × m) :
    (Y * (krausAmp κ K)ᴴ) x y = ∑ j, Y x (y.1, j) * star (K y.2 j) := by
  simp only [Matrix.mul_apply, krausAmp, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fintype.sum_prod_type, apply_ite star, star_zero, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- A Kraus representation of `Φ` amplifies to a Kraus representation of `id_κ ⊗ Φ`. -/
theorem amplify_eq_sum_krausAmp (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {r : ℕ}
    {K : Fin r → Matrix m n ℂ} (hK : ∀ X, Φ X = ∑ k, K k * X * (K k)ᴴ)
    (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix (κ × n) (κ × n) ℂ) :
    amplify Φ κ X = ∑ k, krausAmp κ (K k) * X * (krausAmp κ (K k))ᴴ := by
  ext x y
  simp only [amplify, Matrix.of_apply, hK, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_krausAmp_conjTranspose_apply]
  simp only [krausAmp_mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]

omit [DecidableEq n] [DecidableEq m] in
theorem isCompletelyPositive_of_hasKraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : HasKraus Φ) : IsCompletelyPositive Φ := by
  classical
  obtain ⟨r, K, hK⟩ := h
  intro κ _ X hX
  rw [amplify_eq_sum_krausAmp Φ hK κ X]
  exact Matrix.posSemidef_sum _ fun k _ => hX.mul_mul_conjTranspose_same _

omit [Fintype m] [DecidableEq m] in
theorem maxEnt_posSemidef : (maxEnt n).PosSemidef := by
  have h : maxEnt n = (Matrix.of fun (_ : Unit) x => if x.1 = x.2 then (1 : ℂ) else 0)ᴴ *
      (Matrix.of fun (_ : Unit) x => if x.1 = x.2 then (1 : ℂ) else 0) := by
    ext x y
    simp only [maxEnt, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.univ_unique, Finset.sum_singleton]
    split_ifs <;> simp_all
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [Fintype m] [DecidableEq m] in
/-- Applying `id_n ⊗ Φ` to the maximally entangled state gives exactly the Choi matrix. -/
theorem amplify_maxEnt (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    amplify Φ n (maxEnt n) = choiMatrix Φ := by
  ext x y
  have h : (Matrix.of fun i j => maxEnt n (x.1, i) (y.1, j)) = Matrix.single x.1 y.1 (1 : ℂ) := by
    ext i j
    simp [maxEnt, Matrix.single_apply, eq_comm]
  simp [amplify, choiMatrix, h]

omit [Fintype m] [DecidableEq m] in
theorem choi_posSemidef_of_isCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : IsCompletelyPositive Φ) : (choiMatrix Φ).PosSemidef := by
  have hp := h n (maxEnt n) maxEnt_posSemidef
  rwa [amplify_maxEnt] at hp

omit [DecidableEq m] in
/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
theorem choi_jamiolkowski (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    IsCompletelyPositive Φ ↔ (choiMatrix Φ).PosSemidef :=
  ⟨choi_posSemidef_of_isCompletelyPositive Φ,
    fun h => isCompletelyPositive_of_hasKraus Φ (hasKraus_of_choi_posSemidef Φ h)⟩

omit [DecidableEq m] in
/-- Equivalently: positivity of the Choi matrix characterises the maps with a Kraus
(operator-sum) representation. -/
theorem hasKraus_iff_choi_posSemidef (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    HasKraus Φ ↔ (choiMatrix Φ).PosSemidef :=
  ⟨fun h => choi_posSemidef_of_isCompletelyPositive Φ (isCompletelyPositive_of_hasKraus Φ h),
    hasKraus_of_choi_posSemidef Φ⟩

/-! ### The transpose map is not completely positive

This shows the notions above are not vacuous. -/

/-- The transpose map on matrices, as a linear map. -/
def transposeMap (k : Type) : Matrix k k ℂ →ₗ[ℂ] Matrix k k ℂ where
  toFun A := Aᵀ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The Choi matrix of the transpose map on `2 × 2` matrices (the swap operator) is not
positive semidefinite. -/
theorem choi_transposeMap_not_posSemidef :
    ¬ (choiMatrix (transposeMap (Fin 2))).PosSemidef := by
  intro h
  have hv := h.dotProduct_mulVec_nonneg
    (fun x => if x = (0, 1) then 1 else if x = (1, 0) then -1 else 0)
  simp only [choiMatrix, transposeMap, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.of_apply, Matrix.transpose_apply,
    Matrix.single_apply, LinearMap.coe_mk, AddHom.coe_mk, Pi.star_apply] at hv
  norm_num at hv

/-- Consequently the transpose map is not completely positive. -/
theorem transposeMap_not_isCompletelyPositive :
    ¬ IsCompletelyPositive (transposeMap (Fin 2)) := fun h =>
  choi_transposeMap_not_posSemidef ((choi_jamiolkowski _).mp h)

end QI

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

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

