/-
# Inclusion Exclusion
Category: Pure Mathematics
Target: Math.inclusion_exclusion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses a plain block comment rather than a module docstring `/-! ... -/`,
-- because Lean 4 requires `import` commands to precede every other command in a file.)
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

namespace Math

/-- The alternating sum `∑ (-1)^(|t|+1)` over all *nonempty* subsets `t` of a nonempty
finite set `T` equals `1`.  This is the pointwise combinatorial identity underlying the
inclusion–exclusion principle. -/

theorem alt_sum_nonempty_subsets {ι : Type*} (T : Finset ι) (hT : T.Nonempty) :
    ∑ t ∈ T.powerset.filter (fun t => t.Nonempty), ((-1 : ℤ)) ^ (t.card + 1) = 1 := by
  classical
  have h0 : ∑ t ∈ T.powerset, ((-1 : ℤ)) ^ t.card = 0 :=
    Finset.sum_powerset_neg_one_pow_card_of_nonempty hT
  have hsplit := Finset.sum_filter_add_sum_filter_not T.powerset (fun t => t.Nonempty)
      (fun t => ((-1 : ℤ)) ^ t.card)
  have hemp : T.powerset.filter (fun t => ¬ t.Nonempty) = {∅} := by
    ext t
    simp [Finset.not_nonempty_iff_eq_empty]
    intro h
    subst h
    simp
  rw [hemp] at hsplit
  simp at hsplit
  rw [h0] at hsplit
  have hneg : ∑ t ∈ T.powerset.filter (fun t => t.Nonempty), ((-1 : ℤ)) ^ t.card = -1 := by
    linarith
  have key : ∑ t ∈ T.powerset.filter (fun t => t.Nonempty), ((-1 : ℤ)) ^ (t.card + 1)
      = - ∑ t ∈ T.powerset.filter (fun t => t.Nonempty), ((-1 : ℤ)) ^ t.card := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun t _ => by ring)
  rw [key, hneg]
  ring

/-- For a nonempty `t ⊆ s`, the set of elements of `⋃ i ∈ s, A i` lying in every `A i` with
`i ∈ t` is exactly the intersection `⋂ i ∈ t, A i` (written as `t.inf' ht A`). -/
