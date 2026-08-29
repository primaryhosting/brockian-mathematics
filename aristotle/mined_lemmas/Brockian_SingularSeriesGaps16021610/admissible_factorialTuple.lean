import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- A finite set of natural numbers is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuples conjecture: the associated singular series
is non-zero) when for every prime `p` the elements of `H` omit at least one
residue class modulo `p`. -/

theorem admissible_factorialTuple (k : ℕ) : Admissible (factorialTuple k) := by
  intro p hp
  rcases le_or_gt p k with hle | hgt
  · -- every element is divisible by `p`, so the class of `1` is missed
    refine ⟨1, hp.one_lt, ?_⟩
    intro h hh
    rcases Finset.mem_image.mp hh with ⟨i, _, rfl⟩
    have hdvd : p ∣ k ! := Nat.dvd_factorial hp.pos hle
    have : i * k ! % p = 0 := Nat.mod_eq_zero_of_dvd (hdvd.mul_left i)
    omega
  · exact exists_missed_residue_of_card_lt (by rw [card_factorialTuple]; exact hgt)

/-- **Singular Series Gaps 16021610.**

Two statements about admissible tuples (equivalently, tuples with non-vanishing
Hardy–Littlewood singular series):

* admissibility of `H` is decided by the primes `p ≤ |H|` alone;
* for every `k` there is an admissible `k`-tuple of natural numbers all lying in
  the gap range `[0, (k-1)·k!]`. -/
