import Mathlib

/-!
# Inclusion Exclusion
Category: Pure Mathematics
Target: Math.inclusion_exclusion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Finset

variable {ι α : Type*} [DecidableEq α]

/-- The intersection `⋂ i ∈ t, A i`, realized as a finset by carving it out of the
ambient union `⋃ i ∈ s, A i`.  For a nonempty `t ⊆ s` this is literally the finset
infimum `t.inf' _ A`, as `interOver_eq_inf'` shows. -/
def interOver (s t : Finset ι) (A : ι → Finset α) : Finset α :=
  (s.biUnion A).filter (fun a => ∀ i ∈ t, a ∈ A i)

/-- For a nonempty `t ⊆ s`, `interOver s t A` really is the intersection `⋂ i ∈ t, A i`. -/
theorem interOver_eq_inf' (s t : Finset ι) (A : ι → Finset α) (hts : t ⊆ s)
    (ht : t.Nonempty) : interOver s t A = t.inf' ht A := by
  ext a
  simp only [interOver, Finset.mem_filter, Finset.mem_inf' ht, Finset.mem_biUnion]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨i, hi⟩ := ht
  exact ⟨i, hts hi, h i hi⟩

/-- **Inclusion–exclusion principle.**

`|⋃_{i ∈ s} A i| = ∑_{∅ ≠ t ⊆ s} (-1)^{|t|+1} |⋂_{i ∈ t} A i|`. -/
theorem inclusion_exclusion (s : Finset ι) (A : ι → Finset α) :
    (#(s.biUnion A) : ℤ) =
      ∑ t ∈ s.powerset.filter (fun t => t.Nonempty),
        (-1 : ℤ) ^ (#t + 1) * #(interOver s t A) := by
  rw [Finset.inclusion_exclusion_card_biUnion s A,
    ← Finset.sum_coe_sort (s.powerset.filter (fun t => t.Nonempty))
      (fun t => (-1 : ℤ) ^ (#t + 1) * #(interOver s t A))]
  refine Finset.sum_congr rfl ?_
  rintro ⟨t, ht⟩ -
  have ht' := Finset.mem_filter.1 ht
  rw [interOver_eq_inf' s t A (Finset.mem_powerset.1 ht'.1) ht'.2]

end Math

