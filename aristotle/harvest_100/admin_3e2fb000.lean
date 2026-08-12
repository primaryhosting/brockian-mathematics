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
theorem inclusion_exclusion {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (A : ι → Finset α) :
    (#(s.biUnion A) : ℤ) = ∑ t ∈ s.powerset.filter (·.Nonempty),
      (-1 : ℤ) ^ (#t + 1) * (#{a ∈ s.biUnion A | ∀ i ∈ t, a ∈ A i} : ℤ) := by
  classical
  rw [Finset.inclusion_exclusion_card_biUnion s A,
    ← Finset.sum_attach (s.powerset.filter (·.Nonempty))
      (fun t => (-1 : ℤ) ^ (#t + 1) * (#{a ∈ s.biUnion A | ∀ i ∈ t, a ∈ A i} : ℤ))]
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht : (t : Finset ι).Nonempty := (mem_filter.1 t.2).2
  have hts : (t : Finset ι) ⊆ s := mem_powerset.1 (mem_filter.1 t.2).1
  have hset : (t : Finset ι).inf' ht A = {a ∈ s.biUnion A | ∀ i ∈ (t : Finset ι), a ∈ A i} := by
    apply Finset.ext
    intro a
    simp only [Finset.mem_inf' ht, mem_filter, mem_biUnion]
    refine ⟨fun h => ?_, fun h => h.2⟩
    obtain ⟨i, hi⟩ := ht
    exact ⟨⟨i, hts hi, h i hi⟩, h⟩
  rw [hset]

/-- **Inclusion–exclusion principle**, set version: for finitely many finite sets `A i`
(`i` ranging over a finset `s`), `|⋃ i ∈ s, A i| = ∑_{∅ ≠ t ⊆ s} (-1)^(|t|+1) |⋂ i ∈ t, A i|`,
cardinalities being measured by `Set.ncard`. -/
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

