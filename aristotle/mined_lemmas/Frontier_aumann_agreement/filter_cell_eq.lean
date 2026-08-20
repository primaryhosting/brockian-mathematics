import Mathlib

/-!
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
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

namespace Frontier

variable {Ω : Type*} [DecidableEq Ω]

/-- The prior probability of a (finite) event `S`, computed from the point masses `p`. -/

theorem filter_cell_eq (hI : IsInfoPartition I) (hM : ∀ ω ∈ M, I ω ⊆ M)
    {C : Finset Ω} (hC : C ∈ M.image I) :
    {ω ∈ M | I ω = C} = C := by
  obtain ⟨ω₀, hω₀M, hω₀⟩ := Finset.mem_image.mp hC
  ext ω
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨-, hIω⟩
    exact hIω ▸ hI.1 ω
  · intro hωC
    have hωI : ω ∈ I ω₀ := hω₀ ▸ hωC
    refine ⟨hM ω₀ hω₀M hωI, ?_⟩
    rw [hI.2 ω₀ ω hωI, hω₀]

/-- Summing a function over the cells of a union `M` of cells recovers the sum over `M`. -/
