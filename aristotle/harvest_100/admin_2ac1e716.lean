/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain comment because Lean requires `import` lines to
-- precede any module docstring; the same text is repeated verbatim below.)
import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Matrix Finset
open scoped ComplexOrder MatrixOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Mₙ(ℂ) →ₗ Mₘ(ℂ)`:
`C (i,k) (j,l) = (Φ Eᵢⱼ) k l`, where the `Eᵢⱼ` are the matrix units. -/
def choiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Matrix (n × m) (n × m) ℂ :=
  Matrix.of fun x y => Φ (Matrix.single x.1 y.1 1) x.2 y.2

/-- The ampliation `Φ ⊗ id_d` of `Φ`, acting on `d × d` block matrices with blocks in
`Mₙ(ℂ)` by applying `Φ` to each block. -/
def ampliation (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (d : Type) [Fintype d]
    (A : Matrix (n × d) (n × d) ℂ) : Matrix (m × d) (m × d) ℂ :=
  Matrix.of fun x y => Φ (Matrix.of fun i j => A (i, x.2) (j, y.2)) x.1 y.1

/-- `Φ` is completely positive: every ampliation `Φ ⊗ id_d` maps positive semidefinite
matrices to positive semidefinite matrices. -/
def IsCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ (d : Type) [Fintype d] (A : Matrix (n × d) (n × d) ℂ),
    A.PosSemidef → (ampliation Φ d A).PosSemidef

/-- `Φ` admits a Kraus decomposition `Φ X = ∑ a, Vₐ X Vₐᴴ`. -/
def HasKrausDecomposition (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∃ (N : ℕ) (V : Fin N → Matrix m n ℂ), ∀ X, Φ X = ∑ a, V a * X * (V a)ᴴ

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- Entrywise description of the conjugation `(V ⊗ 1) A (V ⊗ 1)ᴴ`. -/
private lemma kron_conj_apply {d : Type} [Fintype d] [DecidableEq d]
    (V : Matrix m n ℂ) (A : Matrix (n × d) (n × d) ℂ) (x y : m × d) :
    ((Matrix.of fun (u : m × d) (v : n × d) => V u.1 v.1 * (if u.2 = v.2 then 1 else 0)) * A *
      (Matrix.of fun (u : m × d) (v : n × d) => V u.1 v.1 * (if u.2 = v.2 then 1 else 0))ᴴ) x y
      = ∑ i, ∑ j, V x.1 i * A (i, x.2) (j, y.2) * (starRingEnd ℂ) (V y.1 j) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    apply_ite (starRingEnd ℂ), mul_ite, Finset.sum_ite_eq, mul_comm, mul_assoc]
  simp only [Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- Entrywise description of the conjugation `W X Wᴴ`. -/
private lemma matrix_conj_apply (W : Matrix m n ℂ) (X : Matrix n n ℂ) (k l : m) :
    (W * X * Wᴴ) k l = ∑ i, ∑ j, X i j * (W k i * (starRingEnd ℂ) (W l j)) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, mul_assoc, mul_left_comm]
  exact Finset.sum_comm

section

variable (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)

omit [DecidableEq n] [DecidableEq m] in
/-- A map given by a Kraus decomposition is completely positive. -/
theorem isCompletelyPositive_of_hasKrausDecomposition (h : HasKrausDecomposition Φ) :
    IsCompletelyPositive Φ := by
  obtain ⟨N, V, hV⟩ := h
  intro d _ A hA
  classical
  have key : ampliation Φ d A =
      ∑ a : Fin N, (Matrix.of fun (x : m × d) (y : n × d) =>
        V a x.1 y.1 * (if x.2 = y.2 then 1 else 0)) * A *
        (Matrix.of fun (x : m × d) (y : n × d) =>
          V a x.1 y.1 * (if x.2 = y.2 then 1 else 0))ᴴ := by
    ext x y
    simp only [ampliation, Matrix.of_apply, hV, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [kron_conj_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.sum_mul,
      mul_assoc]
    exact Finset.sum_comm
  rw [key]
  refine posSemidef_sum Finset.univ fun a _ => ?_
  have := hA.conjTranspose_mul_mul_same
    ((Matrix.of fun (x : m × d) (y : n × d) => V a x.1 y.1 * (if x.2 = y.2 then 1 else 0))ᴴ)
  simpa using this

/-- If the Choi matrix of `Φ` is positive semidefinite, then `Φ` has a Kraus decomposition. -/
theorem hasKrausDecomposition_of_choiMatrix_posSemidef (h : (choiMatrix Φ).PosSemidef) :
    HasKrausDecomposition Φ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    (Matrix.nonneg_iff_posSemidef.mpr h)
  classical
  set N := Fintype.card (n × m)
  set e : Fin N ≃ (n × m) := (Fintype.equivFin (n × m)).symm
  refine ⟨N, fun a => Matrix.of fun k i => (starRingEnd ℂ) (B (e a) (i, k)), ?_⟩
  intro X
  ext k l
  have hX : Φ X = ∑ i : n, ∑ j : n, X i j • Φ (Matrix.single i j 1) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) by
      rw [Matrix.smul_single]; simp]
    rw [map_smul]
  have hentry : ∀ i j : n, Φ (Matrix.single i j 1) k l
      = ∑ a : Fin N, (starRingEnd ℂ) (B (e a) (i, k)) * B (e a) (j, l) := by
    intro i j
    have : Φ (Matrix.single i j 1) k l = choiMatrix Φ (i, k) (j, l) := rfl
    rw [this, hB]
    simp only [Matrix.mul_apply]
    exact (Equiv.sum_comp e fun c => (starRingEnd ℂ) (B c (i, k)) * B c (j, l)).symm
  rw [hX]
  have hswap : ∀ f : n → n → Fin N → ℂ,
      (∑ i : n, ∑ j : n, ∑ a : Fin N, f i j a) = ∑ a : Fin N, ∑ i : n, ∑ j : n, f i j a := by
    intro f
    rw [show (∑ i : n, ∑ j : n, ∑ a : Fin N, f i j a)
        = ∑ i : n, ∑ a : Fin N, ∑ j : n, f i j a from
      Finset.sum_congr rfl fun i _ => Finset.sum_comm]
    exact Finset.sum_comm
  calc (∑ i : n, ∑ j : n, X i j • Φ (Matrix.single i j 1)) k l
      = ∑ i : n, ∑ j : n, ∑ a : Fin N,
          X i j * ((starRingEnd ℂ) (B (e a) (i, k)) * B (e a) (j, l)) := by
        simp [Matrix.sum_apply, hentry, Finset.mul_sum]
    _ = ∑ a : Fin N, ∑ i : n, ∑ j : n,
          X i j * ((starRingEnd ℂ) (B (e a) (i, k)) * B (e a) (j, l)) := hswap _
    _ = (∑ a : Fin N, (Matrix.of fun k i => (starRingEnd ℂ) (B (e a) (i, k))) * X *
          ((Matrix.of fun k i => (starRingEnd ℂ) (B (e a) (i, k))) : Matrix m n ℂ)ᴴ) k l := by
        rw [Matrix.sum_apply]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [matrix_conj_apply]
        simp

omit [Fintype m] [DecidableEq m] in
/-- If `Φ` is completely positive then its Choi matrix is positive semidefinite. -/
theorem choiMatrix_posSemidef_of_isCompletelyPositive (h : IsCompletelyPositive Φ) :
    (choiMatrix Φ).PosSemidef := by
  classical
  set Ω : Matrix Unit (n × n) ℂ := Matrix.of fun _ x => if x.1 = x.2 then 1 else 0 with hΩ
  have hPSD : (Ωᴴ * Ω).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Ω
  have harg : ∀ p q : n,
      (Matrix.of fun i j => (Ωᴴ * Ω) (i, p) (j, q)) = Matrix.single p q (1 : ℂ) := by
    intro p q
    ext i j
    simp [hΩ, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single_apply, ite_and,
      eq_comm, apply_ite (starRingEnd ℂ)]
    split_ifs <;> rfl
  have hamp : ampliation Φ n (Ωᴴ * Ω) =
      (choiMatrix Φ).submatrix (Equiv.prodComm m n) (Equiv.prodComm m n) := by
    ext x y
    simp only [ampliation, choiMatrix, Matrix.submatrix_apply, Matrix.of_apply,
      Equiv.prodComm_apply, harg]
    rfl
  have hres := h n (Ωᴴ * Ω) hPSD
  rw [hamp] at hres
  exact (Matrix.posSemidef_submatrix_equiv (Equiv.prodComm m n)).mp hres

/-- **Choi–Jamiołkowski**: a linear map between matrix algebras is completely positive
if and only if its Choi matrix is positive semidefinite. -/
theorem choi_jamiolkowski :
    IsCompletelyPositive Φ ↔ (choiMatrix Φ).PosSemidef := by
  constructor
  · exact choiMatrix_posSemidef_of_isCompletelyPositive Φ
  · intro h
    exact isCompletelyPositive_of_hasKrausDecomposition Φ
      (hasKrausDecomposition_of_choiMatrix_posSemidef Φ h)

end

/-- Sanity check: the identity map is completely positive. -/
theorem isCompletelyPositive_id :
    IsCompletelyPositive (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :=
  isCompletelyPositive_of_hasKrausDecomposition _ ⟨1, fun _ => 1, by intro X; simp⟩

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

