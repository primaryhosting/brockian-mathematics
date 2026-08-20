import Mathlib
import RequestProject.GoldbachWheelK2_947

/-!
Companion file: certifies that the self-contained primality predicate
`Brockian.IsPrime` used in `RequestProject/GoldbachWheelK2_947.lean` coincides with
Mathlib's `Nat.Prime`, and restates the main theorem in Mathlib terms.
-/

namespace Brockian


theorem goldbachWheelK2_947_mathlib (n : ℕ) (hev : Even n) (h4 : 4 ≤ n) (hle : n ≤ 2 * 947) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨p, q, hp, hq, hpq⟩ := GoldbachWheelK2_947 n hev.two_dvd h4 hle
  exact ⟨p, q, (isPrime_iff_nat_prime p).mp hp, (isPrime_iff_nat_prime q).mp hq, hpq⟩

end Brockian

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (core Lean only), because Lean requires
`import` commands to precede every other command in a file, and the prescribed
header comment must come first.  Primality is therefore defined here from
scratch; the companion file `RequestProject/GoldbachWheelK2_947Mathlib.lean`
checks that `Brockian.IsPrime` agrees with Mathlib's `Nat.Prime`, and restates
the main theorem in Mathlib terms.
-/

namespace Brockian

/-- `IsPrime n` : `n` is at least `2` and its only proper divisor is `1`. -/
