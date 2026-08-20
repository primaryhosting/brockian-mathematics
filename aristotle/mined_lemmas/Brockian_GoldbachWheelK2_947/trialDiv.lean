import Mathlib
import RequestProject.GoldbachWheelK2_947

/-!
Companion file: certifies that the self-contained primality predicate
`Brockian.IsPrime` used in `RequestProject/GoldbachWheelK2_947.lean` coincides with
Mathlib's `Nat.Prime`, and restates the main theorem in Mathlib terms.
-/

namespace Brockian


def trialDiv (n : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, d =>
      if n < d * d then true
      else if n % d == 0 then false
      else trialDiv n fuel (d + 1)

/-- A fast Boolean primality test by trial division up to the square root. -/
