/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, in the standard trial-division form:
`p` is at least `2` and has no divisor `m` with `2 ≤ m < p`.

This file is deliberately kept free of imports so that the required module
header can be the very first item in the file (Lean forbids `import` after a
module docstring).  The companion file
`RequestProject/GoldbachWheelK2_631_Mathlib.lean` proves
`IsPrimeNat p ↔ Nat.Prime p`, so the statement below is exactly the usual
Goldbach statement phrased with Mathlib's `Nat.Prime`. -/

theorem isPrimeNat_iff_prime (p : ℕ) : IsPrimeNat p ↔ Nat.Prime p := by
  rw [Nat.prime_def_lt']
  constructor
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun m hm hmp hdvd => h m hmp hm (Nat.dvd_iff_mod_eq_zero.mp hdvd)⟩
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun m hmp hm hmod => h m hm hmp (Nat.dvd_iff_mod_eq_zero.mpr hmod)⟩

/-- **Goldbach wheel, K = 2, modulus 631**, stated with Mathlib's `Nat.Prime`:
every even `n` with `4 ≤ n ≤ 631` is a sum of two primes. -/
