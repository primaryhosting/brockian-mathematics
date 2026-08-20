/-
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses a plain block comment: Lean 4 requires `import` to precede any
-- module docstring `/-! ... -/`.)

import Mathlib

namespace Frontier

/-!
## Setting

We work with a one-dimensional Lagrangian mechanical system.  The Lagrangian is a
differentiable function `L : ℝ × ℝ → ℝ` of position and velocity, `DL z` denotes its
(Fréchet) derivative at the phase-space point `z = (x, u)`, so that

* `DL z (1, 0)` is the partial derivative `∂L/∂x`,
* `DL z (0, 1)` is the partial derivative `∂L/∂u` (the momentum).

A smooth infinitesimal symmetry is a vector field `X : ℝ → ℝ` on configuration space,
with derivative `X'`.  Its prolongation to phase space is the vector field
`z = (x, u) ↦ (X x, X' x * u)`, and invariance of the action means that `L` is
annihilated by this prolonged field.

Along a trajectory `q` with velocity `v` satisfying the Euler–Lagrange equation
`d/dt (∂L/∂u) = ∂L/∂x`, the Noether current `(∂L/∂u) * X q` is then conserved.
-/

/-- The Noether current attached to a Lagrangian derivative `DL`, a symmetry generator `X`
and a trajectory `t ↦ (q t, v t)`: the momentum contracted with the symmetry generator. -/

lemma directional_deriv_eq_zero_of_invariant
    (L : ℝ × ℝ → ℝ) (DL : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ))
    (hL : ∀ z, HasFDerivAt L (DL z) z) (X X' : ℝ → ℝ)
    (hinv : ∀ z : ℝ × ℝ,
      HasDerivAt (fun e : ℝ => L (z.1 + e * X z.1, z.2 + e * (X' z.1 * z.2))) 0 0)
    (z : ℝ × ℝ) :
    DL z (X z.1, X' z.1 * z.2) = 0 := by
  have hc : HasDerivAt (fun e : ℝ => ((z.1 + e * X z.1, z.2 + e * (X' z.1 * z.2)) : ℝ × ℝ))
      (X z.1, X' z.1 * z.2) 0 := by
    have h1 : HasDerivAt (fun e : ℝ => z.1 + e * X z.1) (X z.1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (X z.1)).const_add z.1
    have h2 : HasDerivAt (fun e : ℝ => z.2 + e * (X' z.1 * z.2)) (X' z.1 * z.2) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (X' z.1 * z.2)).const_add z.2
    exact h1.prodMk h2
  have hcomp := (hL (z.1 + 0 * X z.1, z.2 + 0 * (X' z.1 * z.2))).comp_hasDerivAt 0 hc
  simp only [zero_mul, add_zero] at hcomp
  exact hcomp.unique (hinv z)

/-- **Key lemma.**  Under the Euler–Lagrange equation and the symmetry (invariance)
condition, the Noether current has vanishing time derivative. -/
