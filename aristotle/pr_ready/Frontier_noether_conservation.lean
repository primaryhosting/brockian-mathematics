/-!
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
Statement: Each smooth symmetry of an action yields a conserved current (Noether, 1D case).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
# Noether's theorem, one-dimensional base case

We formalise the classical (first) Noether theorem for a one-dimensional
mechanical system with Lagrangian `L : ℝ → ℝ → ℝ`, written `L q v`, and a
one-parameter symmetry group whose infinitesimal generator is a vector field
`X : ℝ → ℝ` on configuration space (`δq = X q`).

The data are:

* the partial derivatives `∂L/∂q x u = deriv (fun y => L y u) x` and
  `∂L/∂v x u = deriv (fun w => L x w) u`;
* a trajectory `q` with velocity `v`;
* the Euler–Lagrange equation `d/dt (∂L/∂v (q t) (v t)) = ∂L/∂q (q t) (v t)`;
* the infinitesimal invariance of the Lagrangian under the flow of `X`, i.e.
  the vanishing of `∂L/∂q x u * X x + ∂L/∂v x u * (X' x * u)`, which is exactly
  the statement that `L` is unchanged, to first order, by the substitution
  `(q, v) ↦ (q + s X q, v + s X'(q) v)`.

The conclusion is that the Noether current
`J t = ∂L/∂v (q t) (v t) * X (q t)` (the momentum contracted with the
generator) has vanishing time derivative, and hence is constant along the
trajectory.
-/

namespace Frontier

/-- **Noether's theorem (1D case).**  A smooth symmetry of the action, given
infinitesimally by a vector field `X` on configuration space satisfying the
invariance condition `hsym`, yields a conserved current
`J t = ∂L/∂v (q t) (v t) * X (q t)` along any solution `q` of the
Euler–Lagrange equation `hEL`: the current has vanishing time derivative and
is constant in time. -/
theorem noether_conservation
    (L : ℝ → ℝ → ℝ) (X q v : ℝ → ℝ)
    -- the generator `X` is differentiable
    (hX : ∀ x : ℝ, DifferentiableAt ℝ X x)
    -- `v` is the velocity of the trajectory `q`
    (hq : ∀ t : ℝ, HasDerivAt q (v t) t)
    -- Euler–Lagrange equation for `q`
    (hEL : ∀ t : ℝ, HasDerivAt (fun s => deriv (fun w => L (q s) w) (v s))
      (deriv (fun y => L y (v t)) (q t)) t)
    -- infinitesimal invariance of `L` under the flow of `X`
    (hsym : ∀ x u : ℝ,
      deriv (fun y => L y u) x * X x + deriv (fun w => L x w) u * (deriv X x * u) = 0) :
    (∀ t : ℝ, HasDerivAt (fun s => deriv (fun w => L (q s) w) (v s) * X (q s)) 0 t) ∧
      ∀ t₀ t₁ : ℝ, deriv (fun w => L (q t₀) w) (v t₀) * X (q t₀)
        = deriv (fun w => L (q t₁) w) (v t₁) * X (q t₁) := by
  have key : ∀ t : ℝ,
      HasDerivAt (fun s => deriv (fun w => L (q s) w) (v s) * X (q s)) 0 t := by
    intro t
    have hXq : HasDerivAt (fun s => X (q s)) (deriv X (q t) * v t) t :=
      ((hX (q t)).hasDerivAt).comp t (hq t)
    have h := (hEL t).mul hXq
    rwa [hsym (q t) (v t)] at h
  refine ⟨key, fun t₀ t₁ => ?_⟩
  have := is_const_of_deriv_eq_zero
    (f := fun s => deriv (fun w => L (q s) w) (v s) * X (q s))
    (fun s => (key s).differentiableAt) (fun s => (key s).deriv) t₀ t₁
  simpa using this

/-- Sanity check that the hypotheses of `Frontier.noether_conservation` are
satisfiable: for the free particle `L q v = v ^ 2 / 2` with the translation
generator `X = 1`, the conserved current is the momentum `v t`. -/
example (q v : ℝ → ℝ) (hq : ∀ t : ℝ, HasDerivAt q (v t) t)
    (hEL : ∀ t : ℝ, HasDerivAt v 0 t) :
    ∀ t₀ t₁ : ℝ, v t₀ * 1 = v t₁ * 1 := by
  have hLv : ∀ u : ℝ, deriv (fun w : ℝ => w ^ 2 / 2) u = u := by
    intro u; simp
  have hLq : ∀ x u : ℝ, deriv (fun _ : ℝ => u ^ 2 / 2) x = 0 := by
    intro x u; simp
  have := noether_conservation (fun _ u => u ^ 2 / 2) (fun _ => 1) q v
    (fun x => differentiableAt_const 1) hq
    (by intro t; simpa [hLv, hLq] using hEL t)
    (by intro x u; simp [hLv u, hLq x u])
  simpa [hLv] using this.2

end Frontier

