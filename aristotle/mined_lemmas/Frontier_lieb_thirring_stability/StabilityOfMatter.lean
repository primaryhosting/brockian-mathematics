import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

open MeasureTheory

/-! ## Basic objects -/

/-- Physical space `ℝ^d`, with its Euclidean structure and Lebesgue measure. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Negative part `t⁻ = max (-t) 0` of a real number. -/

def StabilityOfMatter (C : ℝ) : Prop :=
  ∀ (N K : ℕ) (Z : Fin K → ℝ) (R : Fin K → Space 3) (psi : Config N → ℝ),
    (∀ j, 0 ≤ Z j) → (∀ j, Z j ≤ 1) →
    Differentiable ℝ psi → Integrable (fun x => ‖gradient psi x‖ ^ 2) →
    (∫ x, (psi x) ^ 2) = 1 → AntisymmetricWave psi →
    Integrable (fun x => coulombPotential Z R x * (psi x) ^ 2) →
    -C * ((N : ℝ) + K) ≤ manyBodyEnergy Z R psi

/-- **Hardy's inequality** in `ℝ³`: `∫ |u|²/|x|² ≤ 4 ∫ |∇u|²` for `u ∈ H¹(ℝ³)`. -/
