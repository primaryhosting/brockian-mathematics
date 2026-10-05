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

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxRecDepth 100000

namespace Brockian.ZumkellerNumbers

/-- The sum-of-divisors function `σ₁`, written directly as a sum over `Nat.divisors`. -/

theorem two_mul_le_sigmaSum_of_isZumkeller {n : ℕ} (hz : IsZumkeller n) :
    2 * n ≤ sigmaSum n := by
  obtain ⟨hn, S, hS, hsum⟩ := hz
  have h := Finset.sum_sdiff (f := fun d : ℕ => d) hS
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  have hle : n ≤ ∑ d ∈ S, d := by
    by_cases hnS : n ∈ S
    · exact Finset.single_le_sum (f := fun d : ℕ => d) (fun i _ => Nat.zero_le i) hnS
    · have hmem' : n ∈ n.divisors \ S := Finset.mem_sdiff.mpr ⟨hmem, hnS⟩
      rw [hsum]
      exact Finset.single_le_sum (f := fun d : ℕ => d) (fun i _ => Nat.zero_le i) hmem'
  have hsplit : sigmaSum n = ∑ d ∈ S, d + ∑ d ∈ S, d := by
    rw [sigmaSum, ← h, ← hsum]
  omega

/-- Geometric sum identity, in a subtraction-free form. -/
