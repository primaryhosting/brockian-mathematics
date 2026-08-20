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

theorem goldbachWheelK2_iff_odd (m : ℕ) : GoldbachWheelK2 m ↔ Odd m := by
  refine ⟨fun h => ?_, goldbachWheelK2_of_odd⟩
  by_contra hodd
  exact not_goldbachWheelK2_of_two_dvd (Nat.not_odd_iff_even.mp hodd).two_dvd h

/-- **Target.** `947` is a `K2` Goldbach wheel modulus. -/
