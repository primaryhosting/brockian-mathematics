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

lemma exp_neg_beta_work_mul_boltzmann (β : ℝ) (H₀ H₁ : Ω → ℝ) (Φ : Ω → Ω) (x : Ω) :
    Real.exp (-β * work H₀ H₁ Φ x) * Real.exp (-β * H₀ x) = Real.exp (-β * H₁ (Φ x)) := by
  rw [← Real.exp_add]
  congr 1
  simp [work]
  ring

/-- Liouville's theorem (as a hypothesis on `Φ`) gives invariance of the final partition
function under the evolution map. -/
