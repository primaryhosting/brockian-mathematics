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

theorem three_dvd_thd {y : Fin 2 × Bool} {t : List (Fin 2 × Bool)} (hy : y.1 = 0) :
    (3 : ℤ) ∣ (evalW (y :: t)).2.2 := by
  rw [evalW_cons, stp, if_pos hy]
  exact ⟨_, rfl⟩

