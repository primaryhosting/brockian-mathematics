/-
# Inclusion Exclusion
Category: Pure Mathematics
Target: Math.inclusion_exclusion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math

open Finset

/-- **Inclusion–exclusion principle.**

For a finite index set `s` and a family of finite sets `A i` inside a finite type `α`,
the cardinality of the union `⋃ i ∈ s, A i` equals the alternating sum
`∑_{∅ ≠ t ⊆ s} (-1)^(|t|+1) |⋂_{i ∈ t} A i|`.

Here `t.inf A` is the intersection `⋂ i ∈ t, A i` (the infimum in the lattice `Finset α`,
which for the empty index set would be `univ`; empty `t` is excluded by the filter).

Proved from Mathlib's `Finset.inclusion_exclusion_card_biUnion`, restating its `Finset`-subtype
sum as a plain filtered sum and its `Finset.inf'` as `Finset.inf`. -/
theorem inclusion_exclusion {ι α : Type*} [DecidableEq α] [Fintype α]
    (s : Finset ι) (A : ι → Finset α) :
    (#(s.biUnion A) : ℤ) =
      ∑ t ∈ s.powerset with t.Nonempty, (-1 : ℤ) ^ (#t + 1) * #(t.inf A) := by
  classical
  rw [Finset.inclusion_exclusion_card_biUnion s A, ← Finset.sum_attach _
    (fun t => (-1 : ℤ) ^ (#t + 1) * #(t.inf A))]
  refine Finset.sum_congr rfl ?_
  rintro ⟨t, ht⟩ -
  rw [Finset.inf'_eq_inf]

/-- Set-theoretic phrasing of the inclusion–exclusion principle, using `Set.ncard`. -/
theorem inclusion_exclusion_ncard {ι α : Type*} [DecidableEq α] [Fintype α]
    (s : Finset ι) (A : ι → Set α) :
    ((⋃ i ∈ s, A i).ncard : ℤ) =
      ∑ t ∈ s.powerset with t.Nonempty, (-1 : ℤ) ^ (#t + 1) * (⋂ i ∈ t, A i).ncard := by
  classical
  have key := inclusion_exclusion s (fun i => (A i).toFinset)
  have hU : (⋃ i ∈ s, A i).ncard = #(s.biUnion fun i => (A i).toFinset) := by
    rw [← Set.ncard_coe_finset]
    congr 1
    simp
  have hI : ∀ t : Finset ι, (⋂ i ∈ t, A i).ncard
      = #(t.inf fun i => (A i).toFinset) := by
    intro t
    rw [← Set.ncard_coe_finset]
    congr 1
    induction t using Finset.induction with
    | empty => simp
    | insert a t ha ih => simp [Finset.inf_insert, ih]
  rw [hU, key]
  refine Finset.sum_congr rfl ?_
  intro t _
  rw [hI t]

end Math

