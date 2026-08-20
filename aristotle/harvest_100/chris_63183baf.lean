import Mathlib

/-!
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-! ## The three-qubit Hilbert space -/

/-- Computational basis index for three qubits. -/
abbrev Q : Type := Fin 2 × Fin 2 × Fin 2

/-- The Pauli `X` matrix. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The tensor product `A ⊗ B ⊗ C` of three single-qubit operators, acting on `Q`. -/
def tri (A B C : Matrix (Fin 2) (Fin 2) ℂ) : Matrix Q Q ℂ :=
  fun i j => A i.1 j.1 * B i.2.1 j.2.1 * C i.2.2 j.2.2

/-- The (unnormalised) GHZ state `|000⟩ + |111⟩`. -/
def ghz : Q → ℂ := fun i => if i = (0, 0, 0) then 1 else if i = (1, 1, 1) then 1 else 0

/-- The GHZ state is a nonzero vector. -/
theorem ghz_ne_zero : ghz ≠ 0 := by
  intro h
  have h0 : ghz (0, 0, 0) = 0 := by rw [h]; rfl
  simp [ghz] at h0

/-! ## The four GHZ (Mermin) eigenvalue relations -/

/-- `X ⊗ Y ⊗ Y` has the GHZ state as an eigenvector with eigenvalue `-1`. -/
theorem ghz_XYY : (tri pauliX pauliY pauliY).mulVec ghz = -ghz := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ, ghz, tri,
      pauliX, pauliY]

/-- `Y ⊗ X ⊗ Y` has the GHZ state as an eigenvector with eigenvalue `-1`. -/
theorem ghz_YXY : (tri pauliY pauliX pauliY).mulVec ghz = -ghz := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ, ghz, tri,
      pauliX, pauliY]

/-- `Y ⊗ Y ⊗ X` has the GHZ state as an eigenvector with eigenvalue `-1`. -/
theorem ghz_YYX : (tri pauliY pauliY pauliX).mulVec ghz = -ghz := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ, ghz, tri,
      pauliX, pauliY]

/-- `X ⊗ X ⊗ X` has the GHZ state as an eigenvector with eigenvalue `+1`. -/
theorem ghz_XXX : (tri pauliX pauliX pauliX).mulVec ghz = ghz := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ, ghz, tri,
      pauliX]

/-! ## Local hidden variables -/

/-- A deterministic local hidden-variable assignment for the three parties: `x i` is the
predetermined `±1` outcome of an `X` measurement on qubit `i`, and `y i` that of a `Y`
measurement. -/
structure LHV where
  /-- Outcome of the `X` measurement on each qubit. -/
  x : Fin 3 → ℝ
  /-- Outcome of the `Y` measurement on each qubit. -/
  y : Fin 3 → ℝ
  /-- `X` outcomes are `±1`. -/
  hx : ∀ i, x i = 1 ∨ x i = -1
  /-- `Y` outcomes are `±1`. -/
  hy : ∀ i, y i = 1 ∨ y i = -1

/-- The GHZ quantum predictions, as constraints on a local hidden-variable model:
`XYY = YXY = YYX = -1` while `XXX = +1`. -/
def LHV.MerminConstraints (v : LHV) : Prop :=
  v.x 0 * v.y 1 * v.y 2 = -1 ∧
  v.y 0 * v.x 1 * v.y 2 = -1 ∧
  v.y 0 * v.y 1 * v.x 2 = -1 ∧
  v.x 0 * v.x 1 * v.x 2 = 1

/-- No local hidden-variable assignment can reproduce all four GHZ predictions:
multiplying the three `-1` relations gives `x₀x₁x₂ = -1`, contradicting `x₀x₁x₂ = +1`. -/
theorem no_lhv (v : LHV) : ¬ v.MerminConstraints := by
  rintro ⟨h1, h2, h3, h4⟩
  have key : (v.x 0 * v.x 1 * v.x 2) * ((v.y 0) ^ 2 * (v.y 1) ^ 2 * (v.y 2) ^ 2) = -1 := by
    have : (v.x 0 * v.y 1 * v.y 2) * ((v.y 0 * v.x 1 * v.y 2) * (v.y 0 * v.y 1 * v.x 2)) =
        (-1 : ℝ) * ((-1) * (-1)) := by rw [h1, h2, h3]
    nlinarith [this]
  have hy0 : (v.y 0) ^ 2 = 1 := by rcases v.hy 0 with h | h <;> rw [h] <;> norm_num
  have hy1 : (v.y 1) ^ 2 = 1 := by rcases v.hy 1 with h | h <;> rw [h] <;> norm_num
  have hy2 : (v.y 2) ^ 2 = 1 := by rcases v.hy 2 with h | h <;> rw [h] <;> norm_num
  rw [hy0, hy1, hy2, h4] at key
  norm_num at key

/-! ## The Mermin–GHZ paradox -/

/-- **GHZ nonlocality (Mermin's paradox).**

The three-qubit GHZ state `|000⟩ + |111⟩` is a simultaneous eigenvector of the four
commuting observables `X⊗Y⊗Y`, `Y⊗X⊗Y`, `Y⊗Y⊗X` (eigenvalue `-1`) and `X⊗X⊗X`
(eigenvalue `+1`); these are deterministic predictions of quantum mechanics.  Yet no
deterministic local hidden-variable assignment of `±1` outcomes to the local `X` and `Y`
measurements can reproduce all four of them. -/
theorem ghz_nonlocal :
    ghz ≠ 0 ∧
    (tri pauliX pauliY pauliY).mulVec ghz = -ghz ∧
    (tri pauliY pauliX pauliY).mulVec ghz = -ghz ∧
    (tri pauliY pauliY pauliX).mulVec ghz = -ghz ∧
    (tri pauliX pauliX pauliX).mulVec ghz = ghz ∧
    ∀ v : LHV, ¬ v.MerminConstraints :=
  ⟨ghz_ne_zero, ghz_XYY, ghz_YXY, ghz_YYX, ghz_XXX, no_lhv⟩

end QC

