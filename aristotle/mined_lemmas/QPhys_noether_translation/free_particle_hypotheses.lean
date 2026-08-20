/-
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

/-- **Key lemma.** If a Lagrangian `L : ℝ → ℝ → ℝ` (position, velocity) is invariant under
translations of the position variable, then its partial derivative with respect to position
vanishes identically. -/

theorem free_particle_hypotheses (m q₀ v₀ : ℝ) :
    (∀ a x u : ℝ, freeLagrangian m (x + a) u = freeLagrangian m x u) ∧
      (∀ t : ℝ, HasDerivAt
        (fun s : ℝ => deriv (fun u => freeLagrangian m (q₀ + v₀ * s) u) v₀)
        (deriv (fun y : ℝ => freeLagrangian m y v₀) (q₀ + v₀ * t)) t) ∧
      deriv (fun u => freeLagrangian m (q₀ + v₀ * 0) u) v₀ = m * v₀ := by
  refine ⟨fun _ _ _ => rfl, fun t => ?_, deriv_free_particle_kinetic m v₀⟩
  have hmom : (fun s : ℝ => deriv (fun u => freeLagrangian m (q₀ + v₀ * s) u) v₀)
      = fun _ : ℝ => m * v₀ := by
    funext s
    simpa [freeLagrangian] using deriv_free_particle_kinetic m v₀
  rw [hmom, show (fun y : ℝ => freeLagrangian m y v₀) = fun _ : ℝ => m * v₀ ^ 2 / 2 from rfl,
    deriv_const (q₀ + v₀ * t) (m * v₀ ^ 2 / 2)]
  exact hasDerivAt_const t (m * v₀)

end QPhys

import Mathlib

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

