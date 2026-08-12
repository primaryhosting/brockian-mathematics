/-
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Matrix

namespace QC

/-! ## The quantum side: the GHZ state and its Pauli eigenvalue relations -/

/-- Index type for a three-qubit computational basis. -/
abbrev Idx := Fin 2 × Fin 2 × Fin 2

/-- The Pauli `X` observable. -/
noncomputable def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` observable. -/
noncomputable def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Tensor product (Kronecker product) of three single-qubit operators, acting on the
three-qubit space indexed by `Idx`. -/
noncomputable def tensor3 (A B C : Matrix (Fin 2) (Fin 2) ℂ) : Matrix Idx Idx ℂ :=
  fun i j => A i.1 j.1 * B i.2.1 j.2.1 * C i.2.2 j.2.2

/-- The three-qubit GHZ state `(|000⟩ - |111⟩)/√2`. -/
noncomputable def ghz : Idx → ℂ :=
  fun i => if i = (0, 0, 0) then (Real.sqrt 2)⁻¹
           else if i = (1, 1, 1) then -(Real.sqrt 2)⁻¹ else 0

/-- The GHZ state is a nonzero vector (so the eigenvalue relations below are not vacuous). -/
theorem ghz_ne_zero : ghz ≠ 0 := by
  intro h
  have h0 : ghz (0, 0, 0) = 0 := by rw [h]; rfl
  simp only [ghz] at h0
  have : Real.sqrt 2 ≠ 0 := by positivity
  simp [Complex.ofReal_eq_zero, inv_eq_zero, this] at h0

/-- The GHZ state has unit norm. -/
theorem ghz_norm_sq : ∑ i, Complex.normSq (ghz i) = 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp [Fintype.sum_prod_type, Fin.sum_univ_succ, ghz, Complex.normSq_apply]
  nlinarith [h2]

/-- Quantum prediction: `X ⊗ Y ⊗ Y` has the GHZ state as a `+1` eigenvector. -/
theorem ghz_eigen_XYY : tensor3 pauliX pauliY pauliY *ᵥ ghz = ghz := by
  funext i
  obtain ⟨a, b, c⟩ := i
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      tensor3, pauliX, pauliY, ghz]

/-- Quantum prediction: `Y ⊗ X ⊗ Y` has the GHZ state as a `+1` eigenvector. -/
theorem ghz_eigen_YXY : tensor3 pauliY pauliX pauliY *ᵥ ghz = ghz := by
  funext i
  obtain ⟨a, b, c⟩ := i
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      tensor3, pauliX, pauliY, ghz]

/-- Quantum prediction: `Y ⊗ Y ⊗ X` has the GHZ state as a `+1` eigenvector. -/
theorem ghz_eigen_YYX : tensor3 pauliY pauliY pauliX *ᵥ ghz = ghz := by
  funext i
  obtain ⟨a, b, c⟩ := i
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      tensor3, pauliX, pauliY, ghz]

/-- Quantum prediction: `X ⊗ X ⊗ X` has the GHZ state as a `-1` eigenvector. -/
theorem ghz_eigen_XXX : tensor3 pauliX pauliX pauliX *ᵥ ghz = -ghz := by
  funext i
  obtain ⟨a, b, c⟩ := i
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      tensor3, pauliX, ghz]

/-! ## The classical side: local hidden variables cannot match those predictions -/

/-- **Mermin's argument.**

A local hidden-variable model assigns, for each party (`A`, `B`, `C`) and each of the two
measurement settings (`false` = the `X` observable, `true` = the `Y` observable), a
predetermined outcome `±1` that does not depend on the settings chosen by the other parties.

No such assignment reproduces all four GHZ correlations
`XYY = YXY = YYX = +1` and `XXX = -1`: multiplying the first three relations gives
`A X * B X * C X = +1` (each `Y` outcome occurs twice and squares to `1`), which
contradicts the fourth. -/
theorem no_local_hidden_variables
    (A B C : Bool → ℤ)
    (hA : ∀ s, A s = 1 ∨ A s = -1)
    (hB : ∀ s, B s = 1 ∨ B s = -1)
    (hC : ∀ s, C s = 1 ∨ C s = -1) :
    ¬ (A false * B true * C true = 1 ∧
       A true * B false * C true = 1 ∧
       A true * B true * C false = 1 ∧
       A false * B false * C false = -1) := by
  rintro ⟨h1, h2, h3, h4⟩
  rcases hA false with hAf | hAf <;> rcases hA true with hAt | hAt <;>
    rcases hB false with hBf | hBf <;> rcases hB true with hBt | hBt <;>
      rcases hC false with hCf | hCf <;> rcases hC true with hCt | hCt <;>
        simp only [hAf, hAt, hBf, hBt, hCf, hCt] at h1 h2 h3 h4 <;> omega

/-! ## The GHZ (Mermin) paradox -/

/-- **The GHZ / Mermin nonlocality theorem.**

The (nonzero, unit-norm) three-qubit GHZ state `(|000⟩ - |111⟩)/√2` is simultaneously

* a `+1` eigenvector of `X ⊗ Y ⊗ Y`, of `Y ⊗ X ⊗ Y` and of `Y ⊗ Y ⊗ X`, and
* a `-1` eigenvector of `X ⊗ X ⊗ X`,

so measuring those four commuting observable triples on the GHZ state yields the products of
outcomes `+1, +1, +1, -1` *with certainty*.

Yet no local hidden-variable model — a predetermined `±1` outcome `A s`, `B s`, `C s` for each
party and each setting `s` (`false` = `X`, `true` = `Y`), independent of the other parties'
settings — can reproduce these four deterministic correlations.  This is a contradiction with
local realism that requires no inequality and no statistics: a single run suffices. -/
theorem ghz_nonlocal :
    ghz ≠ 0 ∧
    tensor3 pauliX pauliY pauliY *ᵥ ghz = ghz ∧
    tensor3 pauliY pauliX pauliY *ᵥ ghz = ghz ∧
    tensor3 pauliY pauliY pauliX *ᵥ ghz = ghz ∧
    tensor3 pauliX pauliX pauliX *ᵥ ghz = -ghz ∧
    ∀ A B C : Bool → ℤ,
      (∀ s, A s = 1 ∨ A s = -1) → (∀ s, B s = 1 ∨ B s = -1) → (∀ s, C s = 1 ∨ C s = -1) →
      ¬ (A false * B true * C true = 1 ∧
         A true * B false * C true = 1 ∧
         A true * B true * C false = 1 ∧
         A false * B false * C false = -1) :=
  ⟨ghz_ne_zero, ghz_eigen_XYY, ghz_eigen_YXY, ghz_eigen_YYX, ghz_eigen_XXX,
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

