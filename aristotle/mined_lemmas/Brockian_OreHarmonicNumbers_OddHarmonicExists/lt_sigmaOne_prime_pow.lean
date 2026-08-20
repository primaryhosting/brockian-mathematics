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

lemma lt_sigmaOne_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    a + 1 < sigmaOne (p ^ a) := by
  rw [sigmaOne_prime_pow hp]
  have h : ∑ _i ∈ Finset.range (a + 1), 1 < ∑ i ∈ Finset.range (a + 1), p ^ i := by
    refine Finset.sum_lt_sum (fun i _ => Nat.one_le_pow _ _ hp.pos) ⟨1, ?_, ?_⟩
    · simp only [Finset.mem_range]; omega
    · simpa using hp.one_lt
  simpa using h

/-- No prime power `p ^ a` with `a ≥ 1` is an Ore harmonic number. -/
