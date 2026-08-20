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

theorem not_goldbachWheelK2_of_two_dvd {m : ℕ} (hm : 2 ∣ m) : ¬ GoldbachWheelK2 m := by
  intro h
  obtain ⟨p, q, hpN, hqN, hp, hq, hsum⟩ := h 2 1
  have hcast := congrArg (ZMod.castHom hm (ZMod 2)) hsum
  rw [map_add, map_one, map_natCast, map_natCast] at hcast
  have hp1 : ((p : ℕ) : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))]; norm_num
  have hq1 : ((q : ℕ) : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, Nat.odd_iff.mp (hq.odd_of_ne_two (by omega))]; norm_num
  rw [hp1, hq1] at hcast
  exact absurd hcast (by decide)

/-- Characterisation of the `K2` Goldbach wheel moduli: they are exactly the odd numbers. -/
