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
