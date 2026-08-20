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

theorem rotZ_one (h : (1 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = 1) : rotZ 1 0 h = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp

