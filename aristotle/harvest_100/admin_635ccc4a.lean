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
theorem deriv_position_eq_zero_of_translation_invariant
    (L : ℝ → ℝ → ℝ) (hinv : ∀ a x u, L (x + a) u = L x u) (x u : ℝ) :
    deriv (fun y => L y u) x = 0 := by
  have hconst : (fun y => L y u) = fun _ => L 0 u := by
    funext y
    simpa using hinv y 0 u
  rw [hconst]
  simp

/-- **Noether's theorem for translations (1D).**

Let `L : ℝ → ℝ → ℝ` be a Lagrangian, written `L q v` in terms of position and velocity, and let
`q, v : ℝ → ℝ` be a trajectory and its velocity.  The canonical momentum along the trajectory is
`p t = ∂L/∂v (q t, v t)`.

Assuming
* translation invariance: `L (x + a) u = L x u` for all `a, x, u`, and
* the Euler–Lagrange equation: `d/dt (∂L/∂v (q t, v t)) = ∂L/∂q (q t, v t)`,

the momentum is conserved: it takes the same value at all times. -/
theorem noether_translation
    (L : ℝ → ℝ → ℝ) (q v : ℝ → ℝ)
    (hinv : ∀ a x u, L (x + a) u = L x u)
    (hEL : ∀ t, HasDerivAt (fun s => deriv (fun u => L (q s) u) (v s))
        (deriv (fun y => L y (v t)) (q t)) t) :
    ∀ t s, deriv (fun u => L (q t) u) (v t) = deriv (fun u => L (q s) u) (v s) := by
  set p : ℝ → ℝ := fun s => deriv (fun u => L (q s) u) (v s)
  have hzero : ∀ t, HasDerivAt p 0 t := by
    intro t
    have := hEL t
    rwa [deriv_position_eq_zero_of_translation_invariant L hinv] at this
  have hdiff : Differentiable ℝ p := fun t => (hzero t).differentiableAt
  have hderiv : ∀ t, deriv p t = 0 := fun t => (hzero t).deriv
  intro t s
  exact is_const_of_deriv_eq_zero hdiff hderiv t s

/-- The free-particle Lagrangian of mass `m`: `L q v = m * v ^ 2 / 2`, independent of position. -/
noncomputable def freeLagrangian (m : ℝ) : ℝ → ℝ → ℝ := fun _ u => m * u ^ 2 / 2

/-- For the free-particle Lagrangian `L x u = m * u ^ 2 / 2`, the canonical momentum is `m * u`. -/
theorem deriv_free_particle_kinetic (m u : ℝ) :
    deriv (fun w => m * w ^ 2 / 2) u = m * u := by
  have h : HasDerivAt (fun w : ℝ => m * w ^ 2 / 2) (m * (2 * u ^ 1) / 2) u :=
    ((hasDerivAt_pow 2 u).const_mul m).div_const 2
  rw [h.deriv]
  ring

/-- Non-vacuity check: the hypotheses of `noether_translation` are satisfiable.  The free particle
with Lagrangian `L x u = m * u ^ 2 / 2` on the uniform trajectory `q t = q₀ + v₀ * t` with velocity
`v t = v₀` is translation invariant and satisfies the Euler–Lagrange equation, and its conserved
momentum is `m * v₀`. -/
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

