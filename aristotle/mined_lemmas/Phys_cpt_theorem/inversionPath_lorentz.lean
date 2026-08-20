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

open scoped Real
open Matrix

namespace Phys

/-! ## Complexified Minkowski space and the complex Lorentz group -/

/-- Real Minkowski space `ℝ^{1,3}`. -/
abbrev Spacetime := Fin 4 → ℝ

/-- Complexified Minkowski space `ℂ^4`, the domain of the analytically continued
Wightman functions. -/
abbrev CSpace := Fin 4 → ℂ

/-- The Minkowski bilinear form on real Minkowski space (signature `+ - - -`). -/

lemma inversionPath_lorentz (t : ℝ) : IsComplexLorentz (inversionPath t) := by
  intro z w
  have hcs : Complex.cos ((π : ℂ) * (t : ℂ)) ^ 2 + Complex.sin ((π : ℂ) * (t : ℂ)) ^ 2 = 1 := by
    rw [add_comm]; exact Complex.sin_sq_add_cos_sq _
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  simp [cform, inversionPath, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  linear_combination (z 0 * w 0 - z 1 * w 1 - z 2 * w 2 - z 3 * w 3) * hcs
    + ((Complex.sin ((π : ℂ) * (t : ℂ))) ^ 2 * (z 1 * w 1 - z 0 * w 0)) * hI

