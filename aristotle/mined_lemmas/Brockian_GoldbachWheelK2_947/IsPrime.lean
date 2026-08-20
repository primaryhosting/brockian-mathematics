import Mathlib
import RequestProject.GoldbachWheelK2_947

/-!
Companion file: certifies that the self-contained primality predicate
`Brockian.IsPrime` used in `RequestProject/GoldbachWheelK2_947.lean` coincides with
Mathlib's `Nat.Prime`, and restates the main theorem in Mathlib terms.
-/

namespace Brockian


def IsPrime (n : Nat) : Prop := 2 ≤ n ∧ ∀ m, m < n → m ∣ n → m = 1

/-- Trial division: `trialDiv n fuel d` tests that no `e` with `d ≤ e` and `e * e ≤ n`
divides `n`, using at most `fuel` steps. -/
