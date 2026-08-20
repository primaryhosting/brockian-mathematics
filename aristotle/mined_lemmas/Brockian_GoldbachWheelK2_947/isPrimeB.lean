import Mathlib
import RequestProject.GoldbachWheelK2_947

/-!
Companion file: certifies that the self-contained primality predicate
`Brockian.IsPrime` used in `RequestProject/GoldbachWheelK2_947.lean` coincides with
Mathlib's `Nat.Prime`, and restates the main theorem in Mathlib terms.
-/

namespace Brockian


def isPrimeB (n : Nat) : Bool := 2 ≤ n && trialDiv n n 2

