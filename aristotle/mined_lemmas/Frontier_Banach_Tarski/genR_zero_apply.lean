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

theorem genR_zero_apply (b : Bool) (v : E) :
    genR (0, b) v = !₂[(1/3) * v 0 - (sgnR b * (2 * sq2 / 3)) * v 1,
                       (sgnR b * (2 * sq2 / 3)) * v 0 + (1/3) * v 1, v 2] := by
  have h' : (1/3 : ℝ) ^ 2 + (-(2 * Real.sqrt 2 / 3)) ^ 2 = 1 := by
    rw [neg_pow]; simpa using cos_sin_one_third
  cases b
  · have hg : genR ((0 : Fin 2), false) = (rotA)⁻¹ := rfl
    rw [hg, rotA, rotZ_symm _ _ _ h', rotZ_apply]
    ext i; fin_cases i <;> simp [sgnR, sq2]
  · have hg : genR ((0 : Fin 2), true) = rotA := rfl
    rw [hg, rotA, rotZ_apply]
    ext i; fin_cases i <;> simp [sgnR, sq2]

