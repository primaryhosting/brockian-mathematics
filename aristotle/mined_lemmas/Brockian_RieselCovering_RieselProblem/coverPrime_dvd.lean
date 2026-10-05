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

/-
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.RieselCovering

/-- The Riesel number under consideration: `509203`. -/

lemma coverPrime_dvd (n : ℕ) : coverPrime (n % 24) ∣ k * 2 ^ n - 1 := by
  set p := coverPrime (n % 24) with hpdef
  have hmod : (k * 2 ^ n) % p = 1 := by
    rw [Nat.mul_mod, two_pow_mod_period (two_pow_24_mod (n % 24)) n, ← Nat.mul_mod]
    exact cover_residue (Nat.mod_lt _ (by norm_num))
  have hdm := Nat.div_add_mod (k * 2 ^ n) p
  exact ⟨(k * 2 ^ n) / p, by omega⟩

/-- **The Riesel problem, covering-set half.**
`509203` is a Riesel number: for every `n`, the number `509203 * 2 ^ n - 1` is composite
(not prime).  This is witnessed by the covering set `{3, 5, 7, 13, 17, 241}` of primes,
which divides the sequence periodically with period `24`. -/
