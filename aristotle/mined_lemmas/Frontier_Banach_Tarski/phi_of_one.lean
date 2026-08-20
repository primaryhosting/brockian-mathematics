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

@[simp] theorem phi_of_one : phi (FreeGroup.of 1) = rotB := by simp [phi]

/-! ### The integer recursion

Applying the generators to the vector `v₀ = (0,1,0)` produces vectors of the form
`(A √2, B, C √2)/3^k` with `A B C : ℤ`, and for a reduced word `B` is never divisible by `3`. -/

/-- `√2`. -/
