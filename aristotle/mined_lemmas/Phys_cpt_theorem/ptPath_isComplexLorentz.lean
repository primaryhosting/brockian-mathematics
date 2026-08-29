/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
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

namespace Phys

/-! ## Complexified Minkowski space and the complex Lorentz group -/

/-- Complexified Minkowski space `ℂ⁴`. -/
abbrev CVec : Type := Fin 4 → ℂ

/-- The (bilinear, not sesquilinear) Minkowski form of signature `(+,-,-,-)` on complexified
Minkowski space. -/

lemma ptPath_isComplexLorentz (θ : ℝ) : IsComplexLorentz (ptPath θ) := by
  intro x y
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hs : Complex.sin θ ^ 2 + Complex.cos θ ^ 2 = 1 := Complex.sin_sq_add_cos_sq _
  simp [mform, ptPath, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  linear_combination (x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3) * hs
    - Complex.sin (θ : ℂ) ^ 2 * (x 0 * y 0 - x 1 * y 1) * hI

