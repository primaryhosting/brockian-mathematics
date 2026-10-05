/-
# Inclusion Exclusion
Category: Pure Mathematics
Target: Math.inclusion_exclusion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

open Finset

/-- The finset of elements of `⋃ i ∈ s, A i` lying in every `A i` for `i ∈ t` is exactly
`t.inf' ht A`, provided `t` is nonempty and `t ⊆ s`. -/
theorem filter_biUnion_eq_inf' {ι α : Type*} [DecidableEq α] {s t : Finset ι} (hts : t ⊆ s)
    (htne : t.Nonempty) (A : ι → Finset α) :
    ((s.biUnion A).filter (fun a => ∀ i ∈ t, a ∈ A i)) = t.inf' htne A := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.inf'_eq_inf,
    Finset.mem_inf'_iff_forall (s := t)]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    obtain ⟨i, hi⟩ := htne
    exact ⟨⟨i, hts hi, h i hi⟩, h⟩

/-- **Inclusion–exclusion principle.**

For a finite family `A : ι → Finset α` indexed by `i ∈ s`, the cardinality of the union
`⋃ i ∈ s, A i` equals `∑ (-1)^(|t|+1) * |⋂ i ∈ t, A i|`, the sum ranging over the nonempty
subfamilies `t ⊆ s`.

Here the intersection `⋂ i ∈ t, A i` is realised as the finset of elements of the union that
belong to every `A i` with `i ∈ t`.

This is deduced from `Finset.inclusion_exclusion_card_biUnion` in Mathlib. -/
theorem inclusion_exclusion {ι α : Type*} [DecidableEq α] (s : Finset ι) (A : ι → Finset α) :
    ((s.biUnion A).card : ℤ) =
      ∑ t ∈ s.powerset.filter (·.Nonempty),
        (-1) ^ (t.card + 1) *
          ((s.biUnion A).filter (fun a => ∀ i ∈ t, a ∈ A i)).card := by
  rw [Finset.inclusion_exclusion_card_biUnion s A, ← Finset.sum_coe_sort
      (s.powerset.filter (·.Nonempty))
      (fun t => (-1 : ℤ) ^ (t.card + 1) *
        ((s.biUnion A).filter (fun a => ∀ i ∈ t, a ∈ A i)).card)]
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht := Finset.mem_filter.1 t.2
  rw [filter_biUnion_eq_inf' (Finset.mem_powerset.1 ht.1) ht.2]

end Math

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

