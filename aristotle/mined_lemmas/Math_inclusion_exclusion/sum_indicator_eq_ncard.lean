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
