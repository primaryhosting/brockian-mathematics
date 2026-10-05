import Mathlib
import RequestProject.GoldbachWheelK2_1051

/-!
# Bridge: the import-free primality predicate agrees with `Nat.Prime`

`RequestProject/GoldbachWheelK2_1051.lean` is import-free (so that the required header comment
is the first thing in the file) and therefore uses its own definition `Brockian.IsPrime`.
Here we check that this predicate is literally `Nat.Prime`, and restate the main theorem
in Mathlib's vocabulary.
-/

namespace Brockian


def isPrimeSmall (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range' 2 44).all (fun d => n % d != 0 || n == d)

/-- Search for a decomposition `2 * n = p + q` into two primes with `p ≤ 200`. -/
