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
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

open Filter Topology

namespace Brockian.Equidistribution

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` is `< c`. -/

lemma countLT_add_countIco (x : ℕ → ℝ) (N : ℕ) {a b : ℝ} (hab : a ≤ b) :
    countLT x N a + countIco x N a b = countLT x N b := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.range N).filter fun n => Int.fract (x n) < b)
    (p := fun n => Int.fract (x n) < a)
  rw [Finset.filter_filter, Finset.filter_filter] at h
  have h1 : ((Finset.range N).filter
      fun n => Int.fract (x n) < b ∧ Int.fract (x n) < a)
      = (Finset.range N).filter fun n => Int.fract (x n) < a := by
    apply Finset.filter_congr
    intro n _
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨lt_of_lt_of_le h hab, h⟩
  have h2 : ((Finset.range N).filter
      fun n => Int.fract (x n) < b ∧ ¬ Int.fract (x n) < a)
      = (Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b := by
    apply Finset.filter_congr
    intro n _
    simp only [Set.mem_Ico, not_lt]
    exact and_comm
  rw [h1, h2] at h
  exact h

/-- **Pointwise equidistribution.**  If the empirical distribution function converges to `c`
for every level `c` in a dense set `D`, then it converges to `c` for *every* `c ∈ [0,1]`. -/
