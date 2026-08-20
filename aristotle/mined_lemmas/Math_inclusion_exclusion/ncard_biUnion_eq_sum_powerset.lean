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

open Finset

namespace Math

/-- **Inclusion–exclusion principle**: the cardinality of a finite union `⋃ i ∈ s, A i` equals
the alternating sum `∑ (-1)^(|t|+1) * |⋂ i ∈ t, A i|` over the nonempty subsets `t ⊆ s`.

Here the intersection `⋂ i ∈ t, A i` is realised as the finset of elements of the union that
lie in every `A i` with `i ∈ t`; for nonempty `t` this is exactly that intersection. -/

theorem ncard_biUnion_eq_sum_powerset {ι α : Type*}
    (s : Finset ι) (A : ι → Set α) (hA : ∀ i ∈ s, (A i).Finite) :
    ((⋃ i ∈ s, A i).ncard : ℤ) = ∑ t ∈ s.powerset.filter (·.Nonempty),
      (-1 : ℤ) ^ (#t + 1) * ((⋂ i ∈ (t : Finset ι), A i).ncard : ℤ) := by
  classical
  set B : ι → Finset α := fun i => if h : i ∈ s then (hA i h).toFinset else ∅ with hBdef
  have hB : ∀ i ∈ s, ∀ a : α, a ∈ B i ↔ a ∈ A i := by
    intro i hi a; simp [hBdef, hi]
  have hU : ((s.biUnion B : Finset α) : Set α) = ⋃ i ∈ s, A i := by
    ext a
    simp only [coe_biUnion, mem_coe, Set.mem_iUnion]
    exact ⟨fun ⟨i, hi, ha⟩ => ⟨i, hi, (hB i hi a).1 ha⟩,
      fun ⟨i, hi, ha⟩ => ⟨i, hi, (hB i hi a).2 ha⟩⟩
  rw [← hU, Set.ncard_coe_finset, inclusion_exclusion s B]
  refine Finset.sum_congr rfl fun t htmem => ?_
  have ht : t.Nonempty := (mem_filter.1 htmem).2
  have hts : t ⊆ s := mem_powerset.1 (mem_filter.1 htmem).1
  have hcoe : (({a ∈ s.biUnion B | ∀ i ∈ t, a ∈ B i} : Finset α) : Set α) = ⋂ i ∈ t, A i := by
    ext a
    simp only [coe_filter, Set.mem_setOf_eq, mem_biUnion, Set.mem_iInter]
    constructor
    · rintro ⟨-, h⟩ i hi
      exact (hB i (hts hi) a).1 (h i hi)
    · intro h
      obtain ⟨j, hj⟩ := ht
      exact ⟨⟨j, hts hj, (hB j (hts hj) a).2 (h j hj)⟩,
        fun i hi => (hB i (hts hi) a).2 (h i hi)⟩
  rw [← hcoe, Set.ncard_coe_finset]

#print axioms Math.inclusion_exclusion
#print axioms Math.ncard_biUnion_eq_sum_powerset

end Math

