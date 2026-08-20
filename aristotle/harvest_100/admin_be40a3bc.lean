/-
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QC

/-! ## The quantum side: the GHZ state is a joint eigenvector of the Mermin observables -/

/-- Index type for the computational basis of three qubits. -/
abbrev Idx : Type := Fin 2 × Fin 2 × Fin 2

/-- The (unnormalised) GHZ state `|000⟩ + |111⟩`. -/
noncomputable def ghz : Idx → ℂ :=
  fun i => if i = (0, 0, 0) then 1 else if i = (1, 1, 1) then 1 else 0

/-- Pauli `X`. -/
noncomputable def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli `Y`. -/
noncomputable def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Tensor (Kronecker) product of three single-qubit operators. -/
noncomputable def kron3 (P Q R : Matrix (Fin 2) (Fin 2) ℂ) : Matrix Idx Idx ℂ :=
  Matrix.of fun i j => P i.1 j.1 * Q i.2.1 j.2.1 * R i.2.2 j.2.2

lemma ghz_ne_zero : ghz ≠ 0 := by
  intro h
  have : ghz (0, 0, 0) = 0 := by rw [h]; rfl
  simp [ghz] at this

/-- `X ⊗ X ⊗ X` has eigenvalue `+1` on the GHZ state. -/
lemma ghz_eigen_XXX : (kron3 pauliX pauliX pauliX).mulVec ghz = ghz := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, kron3, pauliX, ghz, Fintype.sum_prod_type,
      Fin.sum_univ_succ]

/-- `X ⊗ Y ⊗ Y` has eigenvalue `-1` on the GHZ state. -/
lemma ghz_eigen_XYY : (kron3 pauliX pauliY pauliY).mulVec ghz = -ghz := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, kron3, pauliX, pauliY, ghz, Fintype.sum_prod_type,
      Fin.sum_univ_succ]

/-- `Y ⊗ X ⊗ Y` has eigenvalue `-1` on the GHZ state. -/
lemma ghz_eigen_YXY : (kron3 pauliY pauliX pauliY).mulVec ghz = -ghz := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, kron3, pauliX, pauliY, ghz, Fintype.sum_prod_type,
      Fin.sum_univ_succ]

/-- `Y ⊗ Y ⊗ X` has eigenvalue `-1` on the GHZ state. -/
lemma ghz_eigen_YYX : (kron3 pauliY pauliY pauliX).mulVec ghz = -ghz := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, kron3, pauliX, pauliY, ghz, Fintype.sum_prod_type,
      Fin.sum_univ_succ]

/-! ## The local hidden variable side: Mermin's contradiction

A deterministic local hidden variable model assigns, for each value of the hidden variable,
outcomes `±1` to each of the two possible local measurements (`true` = measure `X`,
`false` = measure `Y`) at each of the three sites, independently of the settings chosen at
the other sites.  The quantum predictions above are deterministic: measuring `X ⊗ Y ⊗ Y`,
`Y ⊗ X ⊗ Y` or `Y ⊗ Y ⊗ X` on the GHZ state gives a product of outcomes equal to `-1` with
certainty, while `X ⊗ X ⊗ X` gives `+1` with certainty.  No local assignment can reproduce
all four of these facts.
-/

/-- **GHZ / Mermin nonlocality.**  There is no deterministic local hidden variable assignment
`A, B, C : Bool → ℤ` of outcomes `±1` (with `true` denoting the `X` measurement and `false`
the `Y` measurement at each site) reproducing the four deterministic GHZ predictions
`XYY = YXY = YYX = -1` and `XXX = +1`. -/
theorem ghz_nonlocal (A B C : Bool → ℤ)
    (hA : ∀ s, A s = 1 ∨ A s = -1)
    (hB : ∀ s, B s = 1 ∨ B s = -1)
    (hC : ∀ s, C s = 1 ∨ C s = -1) :
    ¬ (A true * B false * C false = -1 ∧
       A false * B true * C false = -1 ∧
       A false * B false * C true = -1 ∧
       A true * B true * C true = 1) := by
  rintro ⟨h1, h2, h3, h4⟩
  rcases hA true with hAt | hAt <;> rcases hA false with hAf | hAf <;>
  rcases hB true with hBt | hBt <;> rcases hB false with hBf | hBf <;>
  rcases hC true with hCt | hCt <;> rcases hC false with hCf | hCf <;>
  simp [hAt, hAf, hBt, hBf, hCt, hCf] at h1 h2 h3 h4

/-- Packaged form: the GHZ state is a joint eigenvector of the four Mermin observables with
eigenvalues `-1, -1, -1, +1`, and no local hidden variable model reproduces these outcomes. -/
theorem ghz_nonlocal_of_quantum :
    ((kron3 pauliX pauliY pauliY).mulVec ghz = -ghz ∧
     (kron3 pauliY pauliX pauliY).mulVec ghz = -ghz ∧
     (kron3 pauliY pauliY pauliX).mulVec ghz = -ghz ∧
     (kron3 pauliX pauliX pauliX).mulVec ghz = ghz ∧ ghz ≠ 0) ∧
    ∀ A B C : Bool → ℤ, (∀ s, A s = 1 ∨ A s = -1) → (∀ s, B s = 1 ∨ B s = -1) →
      (∀ s, C s = 1 ∨ C s = -1) →
      ¬ (A true * B false * C false = -1 ∧
         A false * B true * C false = -1 ∧
         A false * B false * C true = -1 ∧
         A true * B true * C true = 1) :=
  ⟨⟨ghz_eigen_XYY, ghz_eigen_YXY, ghz_eigen_YYX, ghz_eigen_XXX, ghz_ne_zero⟩, ghz_nonlocal⟩

end QC

