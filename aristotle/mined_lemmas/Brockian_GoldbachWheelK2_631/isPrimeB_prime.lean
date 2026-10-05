/-
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
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

namespace Brockian

/-! ### A kernel-friendly primality test

Mathlib's `Nat.decidablePrime` instance tests every candidate divisor below `n`, which makes
`by decide` too slow for a few hundred numbers of size ~1300.  We therefore use trial division by
the divisors `d` with `d * d ≤ n`, together with the correctness lemma `isPrimeB_prime`. -/

/-- `trialDivB n k = true` iff no `d ≤ k` with `2 ≤ d` and `d * d ≤ n` divides `n`. -/

lemma isPrimeB_prime {n : ℕ} (hn : n ≤ 1368) (h : isPrimeB n = true) : Nat.Prime n := by
  rw [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, ht⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm hms => ?_⟩
  have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
  have hm36 : m ≤ 36 := by nlinarith
  exact trialDivB_spec n 36 m ht hm hm36 hmm

/-! ### The wheel search -/

/-- The spokes of the wheel: the primes below `100`, used as candidate small summands. -/
