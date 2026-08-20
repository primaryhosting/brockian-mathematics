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

theorem pow_two_ne_one {w : FreeGroup (Fin 2)} (hw : w ≠ 1) : w * w ≠ 1 := by
  intro h
  apply hw
  have h2 : w ^ 2 = (1 : FreeGroup (Fin 2)) ^ 2 := by
    rw [one_pow, pow_two]; exact h
  exact pow_left_injective (n := 2) (by norm_num) h2

