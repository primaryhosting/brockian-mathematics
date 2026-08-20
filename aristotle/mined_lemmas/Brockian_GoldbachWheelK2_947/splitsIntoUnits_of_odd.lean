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

set_option grind.warning false

namespace Brockian

/-- The `K2` Goldbach wheel property at modulus `m`:

every residue class `r` modulo `m` is represented as `p + q` with `p`, `q` prime, where moreover
the two primes may be taken arbitrarily large (larger than any prescribed bound `N`).

This is the "wheel" (residue-class) shadow of the binary Goldbach problem: it says that, modulo
`m`, no congruence obstruction can rule out a representation as a sum of two primes, uniformly in
the size of the primes used. -/

theorem splitsIntoUnits_of_odd : ∀ {m : ℕ}, Odd m → SplitsIntoUnits m := by
  suffices h : ∀ m : ℕ, Odd m → SplitsIntoUnits m from fun {m} => h m
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
      intro hodd
      exact splitsIntoUnits_prime_pow hp ((Nat.odd_pow_iff hn.ne').mp hodd) hn
  | zero => intro h; simp [Nat.odd_iff] at h
  | one => intro _; exact splitsIntoUnits_one
  | coprime a b _ _ hab iha ihb =>
      intro hodd
      exact splitsIntoUnits_mul hab (iha (Nat.odd_mul.mp hodd).1) (ihb (Nat.odd_mul.mp hodd).2)

/-- Every odd modulus is a `K2` Goldbach wheel modulus.  The proof combines the wheel splitting
