import Mathlib

/-!
# Inclusion Exclusion
Category: Pure Mathematics
Target: Math.inclusion_exclusion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset
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

namespace Math

/-- The intersection `⋂_{i ∈ t} A i`, realised as a `Finset` inside the ambient union
`s.biUnion A`.  For nonempty `t ⊆ s` this is exactly the intersection of the `A i`, `i ∈ t`. -/
def interOver {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (A : ι → Finset α) (t : Finset ι) : Finset α :=
  (s.biUnion A).filter (fun a => ∀ i ∈ t, a ∈ A i)

lemma mem_interOver {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (A : ι → Finset α) (t : Finset ι) (a : α) :
    a ∈ interOver s A t ↔ (∃ i ∈ s, a ∈ A i) ∧ ∀ i ∈ t, a ∈ A i := by
  simp [interOver, Finset.mem_filter, Finset.mem_biUnion]

/-- For a nonempty `t ⊆ s`, `interOver s A t` really is the intersection `⋂_{i ∈ t} A i`. -/
lemma interOver_eq_inf' {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (A : ι → Finset α) (t : Finset ι) (ht : t.Nonempty) (hts : t ⊆ s) :
    interOver s A t = t.inf' ht A := by
  ext a
  rw [mem_interOver, Finset.mem_inf']
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨i, hi⟩ := ht
    exact ⟨⟨i, hts hi, h i hi⟩, h⟩

/-- **Inclusion–exclusion principle.**  The cardinality of a finite union `⋃_{i ∈ s} A i`
equals the alternating sum `∑_{∅ ≠ t ⊆ s} (-1)^(|t|+1) |⋂_{i ∈ t} A i|`. -/
theorem inclusion_exclusion {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (A : ι → Finset α) :
    (#(s.biUnion A) : ℤ) =
      ∑ t ∈ s.powerset.filter (fun t => t.Nonempty),
        (-1 : ℤ) ^ (#t + 1) * #(interOver s A t) := by
  classical
  rw [Finset.inclusion_exclusion_card_biUnion s A, ← Finset.sum_attach
    (s.powerset.filter (fun t => t.Nonempty))
    (fun t => (-1 : ℤ) ^ (#t + 1) * #(interOver s A t))]
  refine Finset.sum_congr rfl ?_
  rintro ⟨t, htmem⟩ -
  have h := Finset.mem_filter.1 htmem
  rw [interOver_eq_inf' s A t h.2 (Finset.mem_powerset.1 h.1)]

/-- Sanity check: for two sets, `|A ∪ B| = |A| + |B| - |A ∩ B|`. -/
example :
    ((({0, 1} : Finset (Fin 2)).biUnion
        (fun i => if i = 0 then ({1, 2} : Finset ℕ) else {2, 3})).card : ℤ) = 3 := by
  decide

example :
    (∑ t ∈ ({0, 1} : Finset (Fin 2)).powerset.filter (fun t => t.Nonempty),
      (-1 : ℤ) ^ (t.card + 1) *
        (interOver ({0, 1} : Finset (Fin 2))
          (fun i => if i = 0 then ({1, 2} : Finset ℕ) else {2, 3}) t).card) = 3 := by
  decide

end Math

