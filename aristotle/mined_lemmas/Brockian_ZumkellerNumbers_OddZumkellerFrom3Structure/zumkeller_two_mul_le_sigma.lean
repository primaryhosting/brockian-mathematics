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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian.ZumkellerNumbers

/-- A positive integer `n` is a *Zumkeller number* if its set of divisors can be split into
two parts with equal sums, i.e. there is a set `A` of divisors of `n` whose sum is exactly
half of `σ(n)`. -/

theorem zumkeller_two_mul_le_sigma {n : ℕ} (h : IsZumkeller n) :
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  obtain ⟨hpos, A, hA, hsum⟩ := h
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hpos.ne'
  have key : n ≤ ∑ d ∈ A, d := by
    by_cases hn : n ∈ A
    · exact Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hn
    · have hmem' : n ∈ n.divisors \ A := Finset.mem_sdiff.mpr ⟨hmem, hn⟩
      have h1 : n ≤ ∑ d ∈ n.divisors \ A, d :=
        Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hmem'
      have h2 : ∑ d ∈ n.divisors \ A, d + ∑ d ∈ A, d = ∑ d ∈ n.divisors, d :=
        Finset.sum_sdiff hA
      omega
  omega

/-- A geometric-sum identity, stated without natural subtraction. -/
