/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the required header is
-- repeated verbatim as the module docstring immediately below the import.)

import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
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

namespace QI

open Matrix ComplexOrder

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι]

/-! ## Definitions -/

/-- The **Knill–Laflamme conditions** for a code with orthogonal projector `P` and a set of
error operators `E i`: `P (E i)ᴴ (E j) P = c i j • P` for some matrix of scalars `c`. -/

lemma code_inner_apply {P : Matrix d d ℂ} {E : ι → Matrix d d ℂ} {c : ι → ι → ℂ}
    (hPh : Pᴴ = P) (hKL : ∀ i j, P * (E i)ᴴ * E j * P = c i j • P)
    {u : d → ℂ} (hPu : P *ᵥ u = u) (i j : ι) :
    star (E i *ᵥ u) ⬝ᵥ (E j *ᵥ u) = c i j * (star u ⬝ᵥ u) := by
  have hstar : star u ᵥ* P = star u := by
    conv_lhs => rw [← hPh, ← star_mulVec, hPu]
  have step1 : star (E i *ᵥ u) ⬝ᵥ (E j *ᵥ u) = star u ⬝ᵥ (((E i)ᴴ * E j) *ᵥ u) := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
  have step2 : (P * (E i)ᴴ * E j * P) *ᵥ u = P *ᵥ (((E i)ᴴ * E j) *ᵥ u) := by
    rw [← mulVec_mulVec, hPu, Matrix.mul_assoc, ← mulVec_mulVec]
  have step3 : star u ⬝ᵥ (((E i)ᴴ * E j) *ᵥ u) = star u ⬝ᵥ ((P * (E i)ᴴ * E j * P) *ᵥ u) := by
    conv_rhs => rw [step2, dotProduct_mulVec, hstar]
  rw [step1, step3, hKL i j, smul_mulVec, dotProduct_smul, hPu, smul_eq_mul]

omit [DecidableEq d] [DecidableEq ι] in
/-- The matrix of Knill–Laflamme scalars is positive semidefinite. -/
