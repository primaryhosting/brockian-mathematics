/-
# Inclusion Exclusion
Category: Pure Mathematics
Target: Math.inclusion_exclusion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Inclusion Exclusion

Formalisation of the inclusion-exclusion principle:
`|⋃_{i ∈ s} A i| = Σ_{∅ ≠ t ⊆ s} (−1)^{|t|+1} |⋂_{i ∈ t} A i|`.
-/

open Finset

namespace Math

/-- The intersection `⋂_{i ∈ t} A i`, realised as a `Finset` by carving it out of the
ambient union `⋃_{i ∈ s} A i`.  For nonempty `t ⊆ s` this is genuinely the intersection
of the family `(A i)_{i ∈ t}` (see `Math.iInter_eq_inf'`). -/
def iInterOn {ι α : Type*} [DecidableEq α] (s : Finset ι) (A : ι → Finset α) (t : Finset ι) :
    Finset α :=
  (s.biUnion A).filter (fun a => ∀ i ∈ t, a ∈ A i)

lemma mem_iInterOn {ι α : Type*} [DecidableEq α] {s : Finset ι} {A : ι → Finset α}
    {t : Finset ι} {a : α} :
    a ∈ iInterOn s A t ↔ (∃ i ∈ s, a ∈ A i) ∧ ∀ i ∈ t, a ∈ A i := by
  simp [iInterOn, Finset.mem_filter, Finset.mem_biUnion]

/-- For a nonempty `t ⊆ s`, `iInterOn s A t` is the intersection `⋂_{i ∈ t} A i`. -/
lemma iInterOn_eq_inf' {ι α : Type*} [DecidableEq α] {s : Finset ι} (A : ι → Finset α)
    {t : Finset ι} (hts : t ⊆ s) (ht : t.Nonempty) :
    iInterOn s A t = t.inf' ht A := by
  ext a
  rw [mem_iInterOn, Finset.mem_inf' ht]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨i, hi⟩ := ht
  exact ⟨i, hts hi, h i hi⟩

/-- **Inclusion–exclusion principle**:
`|⋃_{i ∈ s} A i| = Σ_{∅ ≠ t ⊆ s} (−1)^{|t|+1} |⋂_{i ∈ t} A i|`. -/
theorem inclusion_exclusion {ι α : Type*} [DecidableEq α] (s : Finset ι) (A : ι → Finset α) :
    ((s.biUnion A).card : ℤ) =
      ∑ t ∈ s.powerset with t.Nonempty,
        (-1) ^ (t.card + 1) * ((iInterOn s A t).card : ℤ) := by
  rw [Finset.inclusion_exclusion_card_biUnion s A,
    ← Finset.sum_attach (s.powerset.filter (·.Nonempty))]
  refine Finset.sum_congr rfl fun t _ => ?_
  obtain ⟨hts, ht⟩ := Finset.mem_filter.1 t.2
  rw [iInterOn_eq_inf' A (Finset.mem_powerset.1 hts) ht]

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

