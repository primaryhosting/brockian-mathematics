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

theorem goldbachWheelK2_of_odd {m : ℕ} (hm : Odd m) : GoldbachWheelK2 m := by
  haveI : NeZero m := ⟨by rintro rfl; simp [Nat.odd_iff] at hm⟩
  intro N r
  obtain ⟨c, d, hc, hd, hcd⟩ := splitsIntoUnits_of_odd hm r
  obtain ⟨p, hpN, hp, hpc⟩ := Nat.forall_exists_prime_gt_and_eq_mod hc N
  obtain ⟨q, hqN, hq, hqd⟩ := Nat.forall_exists_prime_gt_and_eq_mod hd N
  exact ⟨p, q, hpN, hqN, hp, hq, by rw [hpc, hqd, hcd]⟩

/-- An even modulus is never a `K2` Goldbach wheel modulus: modulo `2` a sum of two primes bigger
than `2` is always even, so the odd residue classes are missed. -/
