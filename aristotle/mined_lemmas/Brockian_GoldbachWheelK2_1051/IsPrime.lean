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


def IsPrime (n : Nat) : Prop := 2 ≤ n ∧ ∀ m : Nat, m ∣ n → m = 1 ∨ m = n

/-- A kernel-friendly primality test: trial division by every `d` with `2 ≤ d ≤ 45`.
It is sound for inputs `n ≤ 2102`, since `46 * 46 = 2116 > 2102`. -/
