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

noncomputable def gibbsDensity (μ : Measure Ω) (β : ℝ) (H : Ω → ℝ) (x : Ω) : ℝ :=
  Real.exp (-β * H x) / partitionFunction μ β H

/-- The work performed on the system along the protocol that drives the Hamiltonian from
`H₀` to `H₁`, where `Φ` is the (Liouville) evolution map of the phase point during the
protocol: `W(x) = H₁ (Φ x) - H₀ x`. -/
