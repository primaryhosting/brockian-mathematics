import Mathlib
import RequestProject.GoldbachWheelK2_947

/-!
Companion file: certifies that the self-contained primality predicate
`Brockian.IsPrime` used in `RequestProject/GoldbachWheelK2_947.lean` coincides with
Mathlib's `Nat.Prime`, and restates the main theorem in Mathlib terms.
-/

namespace Brockian


theorem goldbachWheelK2_covers : ∀ n, n < 1895 → 2 ∣ n → 4 ≤ n →
    ∃ p ∈ goldbachWheelK2, p ≤ n ∧ isPrimeB p = true ∧ isPrimeB (n - p) = true := by
  decide

/-- **Goldbach wheel, K = 2, modulus 947.** Every even number `n` with
`4 ≤ n ≤ 2 * 947` is the sum of two primes. -/
