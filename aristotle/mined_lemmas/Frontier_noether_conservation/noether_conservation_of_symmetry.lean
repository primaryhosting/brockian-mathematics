/-
/-!
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (The header above is wrapped in a plain block comment because Lean 4 requires
-- `import` commands to precede any module docstring `/-! ... -/`.)

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

namespace Frontier

/-!
## Setting

We work with a one–dimensional mechanical system with Lagrangian `L : ℝ → ℝ → ℝ`,
written `L x v` (position `x`, velocity `v`).  Its partial derivatives are given by
functions `L₁` (w.r.t. position) and `L₂` (w.r.t. velocity).

A *path* is `q : ℝ → ℝ` with velocity `v : ℝ → ℝ`, i.e. `q' = v`.
The path is a *stationary point of the action* iff it satisfies the Euler–Lagrange
equation
  `d/dt (L₂ (q t) (v t)) = L₁ (q t) (v t)`.

An infinitesimal (smooth) symmetry is a vector field `X : ℝ → ℝ` on configuration
space, with derivative `X'`.  It acts on curves by `q ↦ q + s • X ∘ q`, hence on the
velocity by `v ↦ v + s • (X' ∘ q) * v`.  Invariance of the action to first order in
`s` is exactly the pointwise identity

  `L₁ x v * X x + L₂ x v * (X' x * v) = 0`.

Noether's theorem: the *current* `J t = L₂ (q t) (v t) * X (q t)` is conserved.
-/

/-- The Noether current attached to a Lagrangian `L` (with velocity–partial `L₂`),
a path `q` with velocity `v`, and an infinitesimal symmetry `X`:
`J t = L₂ (q t) (v t) * X (q t)`, i.e. momentum times the symmetry generator. -/

theorem noether_conservation_of_symmetry
    (L L₁ L₂ : ℝ → ℝ → ℝ) (q v X X' : ℝ → ℝ)
    (hq : ∀ t : ℝ, HasDerivAt q (v t) t)
    (hX : ∀ x : ℝ, HasDerivAt X (X' x) x)
    (hEL : ∀ t : ℝ, HasDerivAt (fun s : ℝ => L₂ (q s) (v s)) (L₁ (q t) (v t)) t)
    (hL : ∀ x u : ℝ, HasFDerivAt (fun p : ℝ × ℝ => L p.1 p.2)
      (L₁ x u • (ContinuousLinearMap.fst ℝ ℝ ℝ) + L₂ x u • (ContinuousLinearMap.snd ℝ ℝ ℝ)) (x, u))
    (hsym : ∀ s x u : ℝ, L (x + s * X x) (u + s * (X' x * u)) = L x u) :
    (∀ t : ℝ, HasDerivAt (noetherCurrent L₂ q v X) 0 t) ∧
      ∀ t₀ t₁ : ℝ, noetherCurrent L₂ q v X t₁ = noetherCurrent L₂ q v X t₀ :=
  noether_conservation L₁ L₂ q v X X' hq hX hEL
    (infinitesimal_invariance_of_symmetry L L₁ L₂ X X' hL hsym)

/-!
## A concrete instance: the free particle

Lagrangian `L x u = u ^ 2 / 2`, translation symmetry `x ↦ x + s` (generator `X = 1`).
The Noether current is the momentum `u`, and along the straight-line solutions
`q t = a + b * t` it is conserved (and equal to `b`).  This checks that the
hypotheses of `noether_conservation_of_symmetry` are satisfiable. -/
