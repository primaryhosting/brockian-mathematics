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
open scoped Classical

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Brockian
namespace ZumkellerNumbers

/-- A positive natural number `n` is a *Zumkeller number* if the set of its divisors can be
split into two parts having the same sum. -/

theorem zumkeller_iff_signedZumkeller {n : ℕ} :
    Zumkeller n ↔ 0 < n ∧ SignedZumkeller n := by
  constructor
  · rintro ⟨hn, A, hA, hsum⟩
    refine ⟨hn, fun d => if d ∈ A then 1 else -1, fun d => by by_cases h : d ∈ A <;> simp [h], ?_⟩
    rw [← Finset.sum_sdiff hA]
    have h1 : ∑ d ∈ n.divisors \ A, (if d ∈ A then (1 : ℤ) else -1) * (d : ℤ)
        = -∑ d ∈ n.divisors \ A, (d : ℤ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun d hd => ?_
      simp only [Finset.mem_sdiff] at hd
      simp [hd.2]
    have h2 : ∑ d ∈ A, (if d ∈ A then (1 : ℤ) else -1) * (d : ℤ) = ∑ d ∈ A, (d : ℤ) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      simp [hd]
    rw [h1, h2]
    have hcast : ((∑ d ∈ A, d : ℕ) : ℤ) = ((∑ d ∈ n.divisors \ A, d : ℕ) : ℤ) := by
      exact_mod_cast hsum
    push_cast at hcast
    omega
  · rintro ⟨hn, f, hf, hsum⟩
    refine ⟨hn, n.divisors.filter (fun d => f d = 1), Finset.filter_subset _ _, ?_⟩
    have hsplit : n.divisors \ n.divisors.filter (fun d => f d = 1)
        = n.divisors.filter (fun d => ¬ f d = 1) := by
      ext d
      simp only [Finset.mem_sdiff, Finset.mem_filter]
      tauto
    have key : ((∑ d ∈ n.divisors.filter (fun d => f d = 1), d : ℕ) : ℤ)
        = ((∑ d ∈ n.divisors \ n.divisors.filter (fun d => f d = 1), d : ℕ) : ℤ) := by
      rw [hsplit]
      push_cast
      rw [← Finset.sum_filter_add_sum_filter_not n.divisors (fun d => f d = 1)
        (fun d => f d * (d : ℤ))] at hsum
      have e1 : ∑ d ∈ n.divisors.filter (fun d => f d = 1), f d * (d : ℤ)
          = ∑ d ∈ n.divisors.filter (fun d => f d = 1), (d : ℤ) := by
        refine Finset.sum_congr rfl fun d hd => ?_
        simp only [Finset.mem_filter] at hd
        rw [hd.2, one_mul]
      have e2 : ∑ d ∈ n.divisors.filter (fun d => ¬ f d = 1), f d * (d : ℤ)
          = -∑ d ∈ n.divisors.filter (fun d => ¬ f d = 1), (d : ℤ) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun d hd => ?_
        simp only [Finset.mem_filter] at hd
        rcases hf d with h | h
        · exact absurd h hd.2
        · rw [h]; ring
      rw [e1, e2] at hsum
      omega
    exact_mod_cast key

/-- Summing an integer-valued function over the divisors of a coprime product `m * n` is the
same as summing over all pairs consisting of a divisor of `m` and a divisor of `n`. -/
