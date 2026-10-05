/-
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- The canonical momentum of a one–dimensional Lagrangian system.

`L t x v` is the Lagrangian evaluated at time `t`, position `x` and velocity `v`,
and `q` is a path.  The canonical momentum along the path is
`p (t) = (∂L/∂v) (t, q t, q̇ t)`. -/
noncomputable def momentum (L : ℝ → ℝ → ℝ → ℝ) (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun v => L t (q t) v) (deriv q t)

/-- The generalized force of a one–dimensional Lagrangian system along a path:
`(∂L/∂x) (t, q t, q̇ t)`. -/
noncomputable def force (L : ℝ → ℝ → ℝ → ℝ) (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun x => L t x (deriv q t)) (q t)

/-- If the Lagrangian is invariant under spatial translations, the generalized force
vanishes identically. -/
theorem force_eq_zero_of_translation_invariant
    (L : ℝ → ℝ → ℝ → ℝ) (q : ℝ → ℝ)
    (hinv : ∀ s t x v, L t (x + s) v = L t x v) (t : ℝ) :
    force L q t = 0 := by
  have hconst : (fun x => L t x (deriv q t)) = fun _ => L t 0 (deriv q t) := by
    funext x
    have := hinv x t 0 (deriv q t)
    simpa using this
  simp [force, hconst]

/-- **Noether's theorem for spatial translations (1D).**

If the Lagrangian `L` is invariant under translations of the position variable
(`hinv`), and the path `q` satisfies the Euler–Lagrange equation
`d/dt (∂L/∂v) = ∂L/∂x` (`hEL`), then the canonical momentum
`p t = (∂L/∂v) (t, q t, q̇ t)` is conserved. -/
theorem noether_translation
    (L : ℝ → ℝ → ℝ → ℝ) (q : ℝ → ℝ)
    (hinv : ∀ s t x v, L t (x + s) v = L t x v)
    (hEL : ∀ t, HasDerivAt (momentum L q) (force L q t) t) :
    ∀ t₁ t₂, momentum L q t₁ = momentum L q t₂ := by
  have hzero : ∀ t, HasDerivAt (momentum L q) 0 t := by
    intro t
    have := hEL t
    rwa [force_eq_zero_of_translation_invariant L q hinv t] at this
  have hdiff : Differentiable ℝ (momentum L q) := fun t => (hzero t).differentiableAt
  have hderiv : ∀ t, deriv (momentum L q) t = 0 := fun t => (hzero t).deriv
  intro t₁ t₂
  exact is_const_of_deriv_eq_zero hdiff hderiv t₁ t₂

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

