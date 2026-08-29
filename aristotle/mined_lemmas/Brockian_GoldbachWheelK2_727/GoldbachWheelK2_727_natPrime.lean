import Mathlib
import RequestProject.GoldbachWheelK2_727

/-!
# Goldbach Wheel K 2 727 — Mathlib bridge

The target theorem `Brockian.GoldbachWheelK2_727` lives in a Mathlib-free file (a module
docstring may not precede `import`, so the required header comment forces that file to be
import-free).  Here we identify the primality predicate used there with Mathlib's
`Nat.Prime` and restate the result accordingly.
-/

namespace Brockian

/-- The from-first-principles primality predicate agrees with Mathlib's `Nat.Prime`. -/

theorem GoldbachWheelK2_727_natPrime :
    ∀ n : ℕ, 2 ≤ n → n ≤ 727 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 2 * n = p + q := by
  intro n h2 h727
  obtain ⟨p, q, hp, hq, hpq⟩ := GoldbachWheelK2_727 n h2 h727
  exact ⟨p, q, isPrimeNat_iff_prime.mp hp, isPrimeNat_iff_prime.mp hq, hpq⟩

#print axioms GoldbachWheelK2_727
#print axioms GoldbachWheelK2_727_natPrime

end Brockian

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Brockian

/-- Primality of a natural number, stated from first principles.
(`Brockian.isPrimeNat_iff_prime` in `RequestProject.GoldbachWheelK2_727Mathlib`
identifies this with Mathlib's `Nat.Prime`.) -/
