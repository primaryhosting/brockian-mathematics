/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to be the first command; the header above is repeated below
-- as a module docstring.)

import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

open Finset

/-! ## Generalities on monochromatic cliques -/

section General

variable {V : Type*} [LinearOrder V] {G : SimpleGraph V}

/-- The set of vertices of `W` adjacent to `v` in `G`. -/

lemma even_sum_nbr_card (G : SimpleGraph V) (W : Finset V) :
    Even (∑ v ∈ W, (nbr G v W).card) := by
  refine ⟨∑ v ∈ W, ∑ w ∈ W, (if G.Adj v w ∧ v < w then 1 else 0), ?_⟩
  have h1 : ∑ v ∈ W, (nbr G v W).card
      = (∑ v ∈ W, ∑ w ∈ W, (if G.Adj v w ∧ v < w then 1 else 0))
        + ∑ v ∈ W, ∑ w ∈ W, (if G.Adj v w ∧ w < v then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [nbr, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases hadj : G.Adj v w
    · rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hlt
      · simp [hadj, hlt, asymm hlt]
      · simp [hadj, hlt, asymm hlt]
    · simp [hadj]
  have h2 : (∑ v ∈ W, ∑ w ∈ W, (if G.Adj v w ∧ w < v then 1 else 0))
      = ∑ v ∈ W, ∑ w ∈ W, (if G.Adj v w ∧ v < w then 1 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [G.adj_comm y x]
  rw [h1, h2]

/-- R(3,4) ≤ 9. -/
