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

theorem not_isOreHarmonic_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    ¬ IsOreHarmonic (p ^ a) := by
  rintro ⟨-, hdvd⟩
  rw [tau_prime_pow hp] at hdvd
  have h1 : sigmaOne (p ^ a) ∣ a + 1 :=
    Nat.Coprime.dvd_of_dvd_mul_left (coprime_sigmaOne_prime_pow hp) hdvd
  have h2 : sigmaOne (p ^ a) ≤ a + 1 := Nat.le_of_dvd (by omega) h1
  exact absurd h2 (not_le.mpr (lt_sigmaOne_prime_pow hp ha))

/-- An Ore harmonic number is never a prime power; in particular every Ore harmonic number
`> 1` has at least two distinct prime factors. -/
