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

theorem isPrimeNat_iff_prime {n : ℕ} : IsPrimeNat n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨h2, hd⟩
    exact Nat.prime_def.mpr ⟨h2, hd⟩
  · intro hp
    exact ⟨hp.two_le, fun d hd => hp.eq_one_or_self_of_dvd d hd⟩

/-- **Goldbach wheel, K = 2, bound 727**, stated with Mathlib's `Nat.Prime`:
every even number `2 * n` with `2 ≤ n ≤ 727` is a sum of two primes. -/
