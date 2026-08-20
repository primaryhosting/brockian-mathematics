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

theorem three_dvd_fst {y : Fin 2 × Bool} {t : List (Fin 2 × Bool)} (hy : y.1 = 1) :
    (3 : ℤ) ∣ (evalW (y :: t)).1 := by
  rw [evalW_cons, stp, if_neg (by rw [hy]; decide)]
  exact ⟨_, rfl⟩

/-- If the first letter of `L` is of type `a`, then the third coordinate is divisible by 3. -/
