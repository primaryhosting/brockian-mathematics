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

theorem genR_one_smul (b : Bool) (A B C : ℤ) :
    (3:ℝ) • genR (1, b) (!₂[(A:ℝ) * sq2, (B:ℝ), (C:ℝ) * sq2])
      = !₂[((stp (1, b) (A, B, C)).1 : ℝ) * sq2, ((stp (1, b) (A, B, C)).2.1 : ℝ),
           ((stp (1, b) (A, B, C)).2.2 : ℝ) * sq2] := by
  rw [genR_one_apply]
  have hs2 : sq2 ^ 2 = 2 := by rw [pow_two]; exact sq2_sq
  ext i
  fin_cases i <;> cases b <;>
    simp [stp, sgnZ, sgnR] <;> ring_nf
  all_goals rw [hs2]; ring

/-- The starting vector `(0,1,0)` of the recursion. -/
