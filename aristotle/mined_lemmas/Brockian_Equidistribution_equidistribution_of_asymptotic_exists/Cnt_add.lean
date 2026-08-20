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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Brockian.Equidistribution

/-- Triangular numbers: `T m = 1 + 2 + ⋯ + m = m (m+1) / 2`. -/

lemma Cnt_add (a b : ℝ) (p q : ℕ) :
    Cnt a b (p + q) =
      Cnt a b p + ((Finset.range q).filter (fun k => u (p + k) ∈ Set.Ico a b)).card := by
  classical
  rw [Cnt, Cnt, Finset.range_add, Finset.filter_union, Finset.card_union_of_disjoint,
    Finset.filter_map, Finset.card_map]
  · rfl
  · apply Finset.disjoint_filter_filter
    simp only [Finset.disjoint_left, Finset.mem_range, Finset.mem_map]
    rintro x hx ⟨y, hy, rfl⟩
    simp only [addLeftEmbedding_apply] at hx ⊢
    omega

/-- The number of points of `{0/L, 1/L, …, (L-1)/L}` in `[a,b)` differs from `(b-a) L`
by at most one. -/
