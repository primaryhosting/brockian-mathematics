import Mathlib

/-!
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
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

namespace Phys

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The (classical) partition function of a Hamiltonian `H` at inverse temperature `β`,
computed against the phase-space (Liouville) measure `μ`:
`Z = ∫ exp (-β * H x) dμ x`. -/

lemma integral_boltzmann_comp_of_measurePreserving
    {μ : Measure Ω} (β : ℝ) (H₁ : Ω → ℝ) (Φ : Ω ≃ᵐ Ω) (hΦ : MeasurePreserving Φ μ μ) :
    ∫ x, Real.exp (-β * H₁ (Φ x)) ∂μ = partitionFunction μ β H₁ :=
  hΦ.integral_comp Φ.measurableEmbedding (fun y => Real.exp (-β * H₁ y))

/-- The average of `exp (-β W)` over the initial canonical ensemble is the ratio of
partition functions `Z₁ / Z₀`. -/
