/- (Lean requires `import` to precede any module docstring, so this required header is
   reproduced verbatim as a plain block comment.)
/-!
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

namespace QC

/-- Index type for the computational basis of three qubits. -/
abbrev Q3 := Fin 2 × Fin 2 × Fin 2

/-- The Pauli `X` matrix. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The tensor (Kronecker) product of three single-qubit operators, acting on the
three-qubit space indexed by `Q3`. -/
def op3 (A B C : Matrix (Fin 2) (Fin 2) ℂ) : Matrix Q3 Q3 ℂ :=
  fun p q => A p.1 q.1 * B p.2.1 q.2.1 * C p.2.2 q.2.2

/-- The three-qubit GHZ state `(|000⟩ + |111⟩)/√2`. -/
noncomputable def ghz : Q3 → ℂ :=
  fun p => if p = (0, 0, 0) then ((Real.sqrt 2)⁻¹ : ℝ)
           else if p = (1, 1, 1) then ((Real.sqrt 2)⁻¹ : ℝ) else 0

/-- The GHZ state is a unit vector. -/
lemma ghz_normalized : ∑ p : Q3, Complex.normSq (ghz p) = 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  simp [ghz, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_apply]
  field_simp
  linarith [h2]

/-- Acting with any operator on the GHZ state only sees its two nonzero components. -/
lemma mulVec_ghz (M : Matrix Q3 Q3 ℂ) (p : Q3) :
    Matrix.mulVec M ghz p = ((Real.sqrt 2)⁻¹ : ℝ) * (M p (0, 0, 0) + M p (1, 1, 1)) := by
  simp [Matrix.mulVec, dotProduct, ghz, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- `X ⊗ Y ⊗ Y` has the GHZ state as an eigenvector with eigenvalue `-1`. -/
lemma ghz_eigen_XYY : Matrix.mulVec (op3 pauliX pauliY pauliY) ghz = -ghz := by
  funext p
  obtain ⟨a, b, c⟩ := p
  rw [mulVec_ghz]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [op3, ghz, pauliX, pauliY]

/-- `Y ⊗ X ⊗ Y` has the GHZ state as an eigenvector with eigenvalue `-1`. -/
lemma ghz_eigen_YXY : Matrix.mulVec (op3 pauliY pauliX pauliY) ghz = -ghz := by
  funext p
  obtain ⟨a, b, c⟩ := p
  rw [mulVec_ghz]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [op3, ghz, pauliX, pauliY]

/-- `Y ⊗ Y ⊗ X` has the GHZ state as an eigenvector with eigenvalue `-1`. -/
lemma ghz_eigen_YYX : Matrix.mulVec (op3 pauliY pauliY pauliX) ghz = -ghz := by
  funext p
  obtain ⟨a, b, c⟩ := p
  rw [mulVec_ghz]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [op3, ghz, pauliX, pauliY]

/-- `X ⊗ X ⊗ X` has the GHZ state as an eigenvector with eigenvalue `+1`. -/
lemma ghz_eigen_XXX : Matrix.mulVec (op3 pauliX pauliX pauliX) ghz = ghz := by
  funext p
  obtain ⟨a, b, c⟩ := p
  rw [mulVec_ghz]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [op3, ghz, pauliX]

/-- **Mermin's argument.** No local hidden-variable model, i.e. no pre-assignment of
deterministic outcomes `x i, y i ∈ {-1, 1}` to the local measurements `X` and `Y` on
each of the three qubits, can reproduce the four GHZ correlations
`XYY = YXY = YYX = -1` and `XXX = +1`: multiplying the first three equations gives
`x 0 * x 1 * x 2 = -1` (each `y i` occurring twice, squaring to `1`), contradicting the
fourth.  (Only the `±1`-valuedness of the `Y`-outcomes `y` is needed for the argument,
so no hypothesis on `x` is imposed.) -/
theorem no_local_hidden_variables (x y : Fin 3 → ℤ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) :
    ¬ (x 0 * y 1 * y 2 = -1 ∧ y 0 * x 1 * y 2 = -1 ∧ y 0 * y 1 * x 2 = -1 ∧
       x 0 * x 1 * x 2 = 1) := by
  rintro ⟨h1, h2, h3, h4⟩
  have key : (x 0 * y 1 * y 2) * ((y 0 * x 1 * y 2) * (y 0 * y 1 * x 2))
      = (x 0 * x 1 * x 2) * ((y 0 * y 0) * ((y 1 * y 1) * (y 2 * y 2))) := by ring
  rw [h1, h2, h3, h4] at key
  rcases hy 0 with h | h <;> rcases hy 1 with h' | h' <;> rcases hy 2 with h'' | h'' <;>
    rw [h, h', h''] at key <;> norm_num at key

/-- **GHZ / Mermin nonlocality.** The three-qubit GHZ state `(|000⟩ + |111⟩)/√2` is a
simultaneous eigenvector of the four commuting Mermin observables `X⊗Y⊗Y`, `Y⊗X⊗Y`,
`Y⊗Y⊗X` (eigenvalue `-1`) and `X⊗X⊗X` (eigenvalue `+1`), so quantum mechanics predicts
those four products with certainty; yet no local hidden-variable assignment of
deterministic outcomes `±1` to the local `X` and `Y` measurements can reproduce all four
predictions. -/
theorem ghz_nonlocal :
    (∑ p : Q3, Complex.normSq (ghz p) = 1) ∧
    Matrix.mulVec (op3 pauliX pauliY pauliY) ghz = -ghz ∧
    Matrix.mulVec (op3 pauliY pauliX pauliY) ghz = -ghz ∧
    Matrix.mulVec (op3 pauliY pauliY pauliX) ghz = -ghz ∧
    Matrix.mulVec (op3 pauliX pauliX pauliX) ghz = ghz ∧
    ∀ x y : Fin 3 → ℤ, (∀ i, y i = 1 ∨ y i = -1) →
      ¬ (x 0 * y 1 * y 2 = -1 ∧ y 0 * x 1 * y 2 = -1 ∧ y 0 * y 1 * x 2 = -1 ∧
         x 0 * x 1 * x 2 = 1) :=
  ⟨ghz_normalized, ghz_eigen_XYY, ghz_eigen_YXY, ghz_eigen_YYX, ghz_eigen_XXX,
    no_local_hidden_variables⟩

end QC

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

