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


def goldbachCheck (n : Nat) : Bool :=
  (List.range' 2 199).any (fun p => isPrimeSmall p && isPrimeSmall (2 * n - p))

/-- Soundness of the trial-division test on the relevant range. -/
