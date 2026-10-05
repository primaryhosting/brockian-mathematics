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

namespace OddZumkeller

/-- A positive natural number `n` is a *Zumkeller number* if its set of divisors can be split
into two parts having the same sum. -/

lemma two_mul_le_sum_divisors_of_zumkeller {n : ℕ} (h : Zumkeller n) :
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  obtain ⟨hn, S, hS, hsum⟩ := h
  have hsplit : (∑ d ∈ n.divisors \ S, d) + (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d :=
    Finset.sum_sdiff hS
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  have hn_le : n ≤ ∑ d ∈ S, d := by
    by_cases hnS : n ∈ S
    · simpa using Finset.single_le_sum (f := fun d : ℕ => d) (fun i _ => Nat.zero_le i) hnS
    · have hmem' : n ∈ n.divisors \ S := Finset.mem_sdiff.mpr ⟨hmem, hnS⟩
      have := Finset.single_le_sum (f := fun d : ℕ => d) (fun i _ => Nat.zero_le i) hmem'
      simp only at this
      omega
  omega

/-- Every prime factor of an odd number is at least `3`. -/
