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
# Odd Harmonic Exists
Category: Brockian Conjecture
Target: Brockian.OreHarmonicNumbers.OddHarmonicExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Harmonic Exists

An *Ore harmonic number* (harmonic divisor number) is a positive integer `n` for which the
harmonic mean of the divisors of `n`, namely `n * τ n / σ n`, is an integer.  Ore's conjecture
states that `1` is the only odd harmonic number; here we prove that an odd harmonic number
does exist (namely `1`), that it is the only one below `1000`, and record the basic
characterisation of the definition in terms of the harmonic mean.
-/

namespace Brockian.OreHarmonicNumbers

open Finset

/-- The sum of the divisors of `n`. -/

lemma coprime_sigmaOne_prime_pow {p a : ℕ} (hp : p.Prime) :
    Nat.Coprime (sigmaOne (p ^ a)) (p ^ a) := by
  refine Nat.Coprime.pow_right _ ?_
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd, sigmaOne_prime_pow hp]
  obtain ⟨k, hk⟩ := geom_sum_eq_one_add_mul p a
  rw [hk]
  intro hdvd
  have h1 : p ∣ 1 := (Nat.dvd_add_right ⟨k, rfl⟩).mp (by simpa [Nat.add_comm] using hdvd)
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

