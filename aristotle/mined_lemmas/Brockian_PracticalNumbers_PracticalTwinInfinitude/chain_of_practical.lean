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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Brockian.PracticalNumbers

/-- A positive natural number `n` is *practical* when every `m ≤ n` can be written as a sum
of distinct divisors of `n`. -/

lemma chain_of_practical {n : ℕ} (hn : Practical n) :
    ∀ x ∈ n.divisors, x ≤ 1 + ∑ y ∈ n.divisors.filter (fun y => y < x), y := by
  obtain ⟨hn0, hrep⟩ := hn
  intro x hx
  by_contra hcon
  push_neg at hcon
  set S := ∑ y ∈ n.divisors.filter (fun y => y < x), y with hSdef
  have hxn : x ≤ n := Nat.le_of_dvd hn0 (Nat.mem_divisors.mp hx).1
  obtain ⟨T, hT, hTsum⟩ := hrep (1 + S) (by omega)
  have hTsub : T ⊆ n.divisors.filter (fun y => y < x) := by
    intro y hy
    refine Finset.mem_filter.mpr ⟨hT hy, ?_⟩
    have : y ≤ ∑ d ∈ T, d := Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i) hy
    omega
  have : (1 : ℕ) + S ≤ S := by
    rw [← hTsum]
    exact Finset.sum_le_sum_of_subset hTsub
  omega

/-- Every `m` up to the sum of divisors of a practical number `n` is a sum of distinct
divisors of `n`. -/
