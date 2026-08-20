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
def IsPrimeNat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m, m < p → 2 ≤ m → p % m ≠ 0

instance (p : Nat) : Decidable (IsPrimeNat p) := by
  unfold IsPrimeNat; infer_instance

/-- `IsSumOfTwoPrimes n` says that `n` is a sum of `K = 2` primes. -/
def IsSumOfTwoPrimes (n : Nat) : Prop :=
  ∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ p + q = n

/-- The `K = 2` Goldbach wheel property at modulus `m`: every even number `n`
with `4 ≤ n ≤ m` is a sum of two primes. -/
def GoldbachWheelK2 (m : Nat) : Prop :=
  ∀ n : Nat, 4 ≤ n → n ≤ m → 2 ∣ n → IsSumOfTwoPrimes n

-- Bounded search form of the wheel statement, verified by kernel evaluation.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem goldbach_search_631 :
    ∀ n, n < 632 → 4 ≤ n → n % 2 = 0 →
      ∃ p, p < n + 1 ∧ IsPrimeNat p ∧ IsPrimeNat (n - p) := by
  decide

/-- **Goldbach wheel, K = 2, modulus 631**: every even `n` with `4 ≤ n ≤ 631`
is a sum of two primes. -/
theorem GoldbachWheelK2_631 : GoldbachWheelK2 631 := by
  intro n h4 h631 hev
  obtain ⟨k, hk⟩ := hev
  obtain ⟨p, hp, hpp, hq⟩ := goldbach_search_631 n (by omega) h4 (by omega)
  exact ⟨p, n - p, hpp, hq, by omega⟩

end Brockian

import Mathlib
import RequestProject.GoldbachWheelK2_631

/-!
# Mathlib bridge for the Goldbach wheel `K = 2`, modulus `631`

The target file `RequestProject/GoldbachWheelK2_631.lean` is import-free (so that
its required module header can be the first item in the file), and therefore uses
its own trial-division definition of primality, `Brockian.IsPrimeNat`.

Here we check that this notion coincides with Mathlib's `Nat.Prime`, and restate
the main theorem in Mathlib terms.
-/

namespace Brockian

/-- The import-free primality predicate agrees with Mathlib's `Nat.Prime`. -/
theorem isPrimeNat_iff_prime (p : ℕ) : IsPrimeNat p ↔ Nat.Prime p := by
  rw [Nat.prime_def_lt']
  constructor
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun m hm hmp hdvd => h m hmp hm (Nat.dvd_iff_mod_eq_zero.mp hdvd)⟩
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun m hmp hm hmod => h m hm hmp (Nat.dvd_iff_mod_eq_zero.mpr hmod)⟩

/-- **Goldbach wheel, K = 2, modulus 631**, stated with Mathlib's `Nat.Prime`:
every even `n` with `4 ≤ n ≤ 631` is a sum of two primes. -/
theorem goldbachWheelK2_631_mathlib (n : ℕ) (h4 : 4 ≤ n) (h631 : n ≤ 631) (hev : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨p, q, hp, hq, hpq⟩ := GoldbachWheelK2_631 n h4 h631 hev.two_dvd
  exact ⟨p, q, (isPrimeNat_iff_prime p).mp hp, (isPrimeNat_iff_prime q).mp hq, hpq⟩

end Brockian

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

