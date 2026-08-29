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
theorem filter_biUnion_eq_inf' {ι α : Type*} [DecidableEq α] (s : Finset ι) (A : ι → Finset α)
    (t : Finset ι) (ht : t.Nonempty) (hts : t ⊆ s) :
    (s.biUnion A).filter (fun a => ∀ i ∈ t, a ∈ A i) = t.inf' ht A := by
  classical
  ext a
  simp only [Finset.mem_filter, Finset.mem_inf', Finset.mem_biUnion]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨i, hi⟩ := ht
    exact ⟨⟨i, hts hi, h i hi⟩, h⟩

/-- **Inclusion–exclusion principle.**  For a finite index set `s` and finite sets `A i`,
the cardinality of the union `⋃ i ∈ s, A i` equals
`∑_{∅ ≠ t ⊆ s} (-1)^(|t|+1) * |⋂_{i ∈ t} A i|`.
The intersection `⋂_{i ∈ t} A i` is expressed as the set of elements of the union belonging to
every `A i` for `i ∈ t`; `Math.filter_biUnion_eq_inf'` shows this is literally the intersection. -/
theorem inclusion_exclusion {ι α : Type*} [DecidableEq α] (s : Finset ι) (A : ι → Finset α) :
    (((s.biUnion A).card : ℤ)) =
      ∑ t ∈ s.powerset.filter (fun t => t.Nonempty),
        (-1 : ℤ) ^ (t.card + 1) *
          (((s.biUnion A).filter (fun a => ∀ i ∈ t, a ∈ A i)).card : ℤ) := by
  classical
  have hcard : ∀ t : Finset ι,
      (((s.biUnion A).filter (fun a => ∀ i ∈ t, a ∈ A i)).card : ℤ)
        = ∑ a ∈ s.biUnion A, if (∀ i ∈ t, a ∈ A i) then (1 : ℤ) else 0 := by
    intro t
    rw [Finset.card_filter]
    push_cast
    simp
  calc (((s.biUnion A).card : ℤ))
      = ∑ _a ∈ s.biUnion A, (1 : ℤ) := by simp
    _ = ∑ a ∈ s.biUnion A, ∑ t ∈ s.powerset.filter (fun t => t.Nonempty),
          (-1 : ℤ) ^ (t.card + 1) * (if (∀ i ∈ t, a ∈ A i) then (1 : ℤ) else 0) := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        have hTa : (s.filter (fun i => a ∈ A i)).Nonempty := by
          simp only [Finset.mem_biUnion] at ha
          obtain ⟨i, hi, hai⟩ := ha
          exact ⟨i, by simp [hi, hai]⟩
        have hset : (s.powerset.filter (fun t => t.Nonempty)).filter
            (fun t => ∀ i ∈ t, a ∈ A i)
            = (s.filter (fun i => a ∈ A i)).powerset.filter (fun t => t.Nonempty) := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff,
            Finset.mem_filter]
          aesop
        have h1 := alt_sum_nonempty_subsets (s.filter (fun i => a ∈ A i)) hTa
        rw [← hset, Finset.sum_filter] at h1
        refine h1.symm.trans (Finset.sum_congr rfl (fun t _ => ?_))
        by_cases h : ∀ i ∈ t, a ∈ A i <;> simp [h]
    _ = ∑ t ∈ s.powerset.filter (fun t => t.Nonempty), ∑ a ∈ s.biUnion A,
          (-1 : ℤ) ^ (t.card + 1) * (if (∀ i ∈ t, a ∈ A i) then (1 : ℤ) else 0) :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [hcard, Finset.mul_sum]

end Math

#print axioms Math.inclusion_exclusion

