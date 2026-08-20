import Mathlib

/-!
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
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

/-- The partial derivative of a Lagrangian `L : ℝ × ℝ → ℝ` with respect to its first
(position) argument, at the point `z = (q, v)`. -/

theorem noether_free_particle (c : ℝ) :
    (∀ t : ℝ, HasDerivAt (fun t : ℝ => c * t) c t) ∧
    (∀ x : ℝ, DifferentiableAt ℝ (fun _ : ℝ => (1 : ℝ)) x) ∧
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => Frontier.dL_dv L (c * s, c))
      (Frontier.dL_dq L (c * t, c)) t) ∧
    (∀ z : ℝ × ℝ, fderiv ℝ L z ((fun _ : ℝ => (1 : ℝ)) z.1,
      deriv (fun _ : ℝ => (1 : ℝ)) z.1 * z.2) = 0) ∧
    (∀ t : ℝ, Frontier.noetherCurrent L (fun _ => 1) (fun t => c * t) (fun _ => c) t
      = 2 * c) := by
  refine ⟨fun t => by simpa using (hasDerivAt_id t).const_mul c,
    fun x => differentiableAt_const 1, ?_, ?_, ?_⟩
  · intro t
    simp only [Frontier.dL_dv, Frontier.dL_dq, fderiv_L_apply]
    simpa using hasDerivAt_const t (2 * c * 1)
  · intro z
    simp [fderiv_L_apply]
  · intro t
    simp [Frontier.noetherCurrent, Frontier.dL_dv, fderiv_L_apply]

end FreeParticle

end Frontier

