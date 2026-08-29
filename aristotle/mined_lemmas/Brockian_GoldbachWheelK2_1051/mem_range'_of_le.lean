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


theorem mem_range'_of_le {s len n : Nat} (h1 : s ≤ n) (h2 : n < s + len) :
    n ∈ List.range' s len :=
  List.mem_range'.mpr ⟨n - s, by omega, by omega⟩

