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

lemma mem_interOver {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (A : ι → Finset α) (t : Finset ι) (a : α) :
    a ∈ interOver s A t ↔ (∃ i ∈ s, a ∈ A i) ∧ ∀ i ∈ t, a ∈ A i := by
  simp [interOver, Finset.mem_filter, Finset.mem_biUnion]

/-- For a nonempty `t ⊆ s`, `interOver s A t` really is the intersection `⋂_{i ∈ t} A i`. -/
