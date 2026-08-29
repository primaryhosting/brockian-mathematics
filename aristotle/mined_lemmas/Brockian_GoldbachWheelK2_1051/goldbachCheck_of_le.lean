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


theorem goldbachCheck_of_le {n : Nat} (hn : 2 ≤ n) (hle : n ≤ 1051) : goldbachCheck n = true := by
  have key : ∀ {s : Nat}, (List.range' s 175).all goldbachCheck = true → s ≤ n → n < s + 175 →
      goldbachCheck n = true := fun h h1 h2 =>
    List.all_eq_true.mp h n (mem_range'_of_le h1 h2)
  rcases (by omega : n < 177 ∨ (177 ≤ n ∧ n < 352) ∨ (352 ≤ n ∧ n < 527) ∨
      (527 ≤ n ∧ n < 702) ∨ (702 ≤ n ∧ n < 877) ∨ (877 ≤ n ∧ n < 1052)) with
    h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
  · exact key check_chunk₁ hn (by omega)
  · exact key check_chunk₂ h (by omega)
  · exact key check_chunk₃ h (by omega)
  · exact key check_chunk₄ h (by omega)
  · exact key check_chunk₅ h (by omega)
  · exact key check_chunk₆ h (by omega)

/-- **Goldbach wheel, `K = 2`, modulus `1051`:** every even number `m` with
`4 ≤ m ≤ 2 * 1051` is the sum of two primes. -/
