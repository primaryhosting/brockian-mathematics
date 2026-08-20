import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem genR_one_apply (b : Bool) (v : E) :
    genR (1, b) v = !₂[v 0, (1/3) * v 1 - (sgnR b * (2 * sq2 / 3)) * v 2,
                       (sgnR b * (2 * sq2 / 3)) * v 1 + (1/3) * v 2] := by
  have h' : (1/3 : ℝ) ^ 2 + (-(2 * Real.sqrt 2 / 3)) ^ 2 = 1 := by
    rw [neg_pow]; simpa using cos_sin_one_third
  cases b
  · have hg : genR ((1 : Fin 2), false) = (rotB)⁻¹ := rfl
    rw [hg, rotB, rotX_symm _ _ _ h', rotX_apply]
    ext i; fin_cases i <;> simp [sgnR, sq2]
  · have hg : genR ((1 : Fin 2), true) = rotB := rfl
    rw [hg, rotB, rotX_apply]
    ext i; fin_cases i <;> simp [sgnR, sq2]

