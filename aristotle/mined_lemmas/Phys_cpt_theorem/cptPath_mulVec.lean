/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

open Finset Matrix

/-- Complexified Minkowski space: four complex coordinates. -/
abbrev CMinkowski : Type := Fin 4 → ℂ

/-- The Minkowski metric signature `(+,-,-,-)`. -/

lemma cptPath_mulVec (t : ℝ) (x : CMinkowski) :
    (cptPath t).mulVec x =
      ![(Real.cos t : ℂ) * x 0 + Complex.I * (Real.sin t : ℂ) * x 1,
        Complex.I * (Real.sin t : ℂ) * x 0 + (Real.cos t : ℂ) * x 1,
        (Real.cos t : ℂ) * x 2 - (Real.sin t : ℂ) * x 3,
        (Real.sin t : ℂ) * x 2 + (Real.cos t : ℂ) * x 3] := by
  funext i
  fin_cases i <;>
    (simp [Matrix.mulVec, cptPath, dotProduct, Fin.sum_univ_four]; try ring)

