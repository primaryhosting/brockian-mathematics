import Mathlib

/-!
# Inclusion Exclusion
Category: Pure Mathematics
Target: Math.inclusion_exclusion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset

/-- Summing the (integer-valued) indicator function of a set `X` over a finset `U`
containing `X` computes the cardinality of `X`. -/
lemma sum_indicator_eq_ncard {α : Type*} {X : Set α} {U : Finset α} (h : X ⊆ (U : Set α)) :
    ∑ a ∈ U, Set.indicator X (1 : α → ℤ) a = (X.ncard : ℤ) := by
  classical
  have hXfin : X.Finite := Set.Finite.subset U.finite_toSet h
  have hfilter : U.filter (fun a => a ∈ X) = hXfin.toFinset := by
    ext a
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun ha => ha.2, fun ha => ⟨h ha, ha⟩⟩
  calc ∑ a ∈ U, Set.indicator X (1 : α → ℤ) a
      = ∑ a ∈ U, if a ∈ X then (1 : ℤ) else 0 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases ha : a ∈ X <;> simp [Set.indicator, ha]
    _ = (#(U.filter (fun a => a ∈ X)) : ℤ) := by
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
        simp
    _ = (X.ncard : ℤ) := by
        rw [hfilter, Set.ncard_eq_toFinset_card X hXfin]

/-- **Inclusion–exclusion principle**:
`|⋃ i ∈ s, A i| = ∑_{∅ ≠ t ⊆ s} (-1)^(|t|+1) |⋂ i ∈ t, A i|`,
for a finite index set `s` and finite sets `A i`. -/
theorem inclusion_exclusion {ι α : Type*} (s : Finset ι) (A : ι → Set α)
    (hA : ∀ i ∈ s, (A i).Finite) :
    ((⋃ i ∈ s, A i).ncard : ℤ) =
      ∑ t ∈ s.powerset with t.Nonempty, (-1) ^ (#t + 1) * ((⋂ i ∈ t, A i).ncard : ℤ) := by
  classical
  have hUfin : (⋃ i ∈ s, A i).Finite := Set.Finite.biUnion s.finite_toSet (by simpa using hA)
  set U : Finset α := hUfin.toFinset with hU
  have hsub : (⋃ i ∈ s, A i) ⊆ (U : Set α) := by
    intro a ha; simp [hU, ha]
  have key : ∀ a ∈ U, Set.indicator (⋃ i ∈ s, A i) (1 : α → ℤ) a
      = ∑ t ∈ s.powerset with t.Nonempty,
        (-1) ^ (#t + 1) * Set.indicator (⋂ i ∈ t, A i) (1 : α → ℤ) a := by
    intro a _
    have := Finset.indicator_biUnion_eq_sum_powerset s A (fun _ => (1 : ℤ)) a
    simpa [zsmul_eq_mul] using this
  have hsum := Finset.sum_congr rfl key
  rw [sum_indicator_eq_ncard hsub] at hsum
  rw [hsum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [Finset.mem_filter, Finset.mem_powerset] at ht
  obtain ⟨hts, htne⟩ := ht
  have hsubt : (⋂ i ∈ t, A i) ⊆ (U : Set α) := by
    obtain ⟨i, hi⟩ := htne
    refine subset_trans ?_ hsub
    intro a ha
    simp only [Set.mem_iInter] at ha
    exact Set.mem_biUnion (hts hi) (ha i hi)
  rw [← Finset.mul_sum, sum_indicator_eq_ncard hsubt]

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

