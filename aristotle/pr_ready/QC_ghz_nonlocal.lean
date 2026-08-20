/-!
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Statement: The 3-qubit GHZ state yields a deterministic Mermin paradox contradiction with local hidden variables.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace QC

open Matrix Complex
open scoped Kronecker

/-- The Pauli `X` matrix. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- Index type for three qubits. -/
abbrev Idx := Fin 2 × Fin 2 × Fin 2

/-- Tensor product (Kronecker product) of three single-qubit operators. -/
def op3 (A B C : Matrix (Fin 2) (Fin 2) ℂ) : Matrix Idx Idx ℂ := A ⊗ₖ (B ⊗ₖ C)

/-- The (unnormalised) GHZ state `|000⟩ + |111⟩`. -/
def ghz : Idx → ℂ := fun p => if p = (0, 0, 0) then 1 else if p = (1, 1, 1) then 1 else 0

theorem ghz_ne_zero : ghz ≠ 0 := by
  intro h
  have := congrFun h (0, 0, 0)
  simp [ghz] at this

theorem ghz_XYY : (op3 pauliX pauliY pauliY) *ᵥ ghz = -ghz := by
  funext p
  fin_cases p <;>
    simp [op3, ghz, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      pauliX, pauliY, Matrix.kroneckerMap]

theorem ghz_YXY : (op3 pauliY pauliX pauliY) *ᵥ ghz = -ghz := by
  funext p
  fin_cases p <;>
    simp [op3, ghz, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      pauliX, pauliY, Matrix.kroneckerMap]

theorem ghz_YYX : (op3 pauliY pauliY pauliX) *ᵥ ghz = -ghz := by
  funext p
  fin_cases p <;>
    simp [op3, ghz, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      pauliX, pauliY, Matrix.kroneckerMap]

theorem ghz_XXX : (op3 pauliX pauliX pauliX) *ᵥ ghz = ghz := by
  funext p
  fin_cases p <;>
    simp [op3, ghz, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      pauliX, Matrix.kroneckerMap]

/-- Mermin's algebraic contradiction: no assignment of definite `±1` values `x i` (for the
`X` measurement on qubit `i`) and `y i` (for the `Y` measurement on qubit `i`) can reproduce
the GHZ correlations `XYY = YXY = YYX = -1`, `XXX = +1`. -/
theorem no_local_hidden_variables (x y : Fin 3 → ℤ)
    (hx : ∀ i, x i = 1 ∨ x i = -1) (hy : ∀ i, y i = 1 ∨ y i = -1) :
    ¬ (x 0 * y 1 * y 2 = -1 ∧ y 0 * x 1 * y 2 = -1 ∧ y 0 * y 1 * x 2 = -1 ∧
       x 0 * x 1 * x 2 = 1) := by
  rintro ⟨h1, h2, h3, h4⟩
  rcases hx 0 with hx0 | hx0 <;> rcases hx 1 with hx1 | hx1 <;> rcases hx 2 with hx2 | hx2 <;>
    rcases hy 0 with hy0 | hy0 <;> rcases hy 1 with hy1 | hy1 <;> rcases hy 2 with hy2 | hy2 <;>
      rw [hx0, hx1, hx2] at h4 <;>
      simp_all

/-- **GHZ nonlocality (Mermin's paradox).**

The GHZ state `|000⟩ + |111⟩` is a simultaneous eigenvector of the four observables
`X⊗Y⊗Y`, `Y⊗X⊗Y`, `Y⊗Y⊗X` (eigenvalue `-1`) and `X⊗X⊗X` (eigenvalue `+1`), so quantum
mechanics predicts these four products of measurement outcomes with certainty; yet no local
hidden-variable model, i.e. no predetermined `±1` outcomes `x i`, `y i` for the local `X` and
`Y` measurements, can reproduce all four predictions. -/
theorem ghz_nonlocal :
    (ghz ≠ 0 ∧
     (op3 pauliX pauliY pauliY) *ᵥ ghz = -ghz ∧
     (op3 pauliY pauliX pauliY) *ᵥ ghz = -ghz ∧
     (op3 pauliY pauliY pauliX) *ᵥ ghz = -ghz ∧
     (op3 pauliX pauliX pauliX) *ᵥ ghz = ghz) ∧
    ∀ x y : Fin 3 → ℤ, (∀ i, x i = 1 ∨ x i = -1) → (∀ i, y i = 1 ∨ y i = -1) →
      ¬ (x 0 * y 1 * y 2 = -1 ∧ y 0 * x 1 * y 2 = -1 ∧ y 0 * y 1 * x 2 = -1 ∧
         x 0 * x 1 * x 2 = 1) :=
  ⟨⟨ghz_ne_zero, ghz_XYY, ghz_YXY, ghz_YYX, ghz_XXX⟩, no_local_hidden_variables⟩

end QC
#print axioms QC.ghz_nonlocal


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

