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

lemma prolonged_apply (DL : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ)) (X X' : ℝ → ℝ) (z : ℝ × ℝ) :
    DL z (X z.1, X' z.1 * z.2)
      = X z.1 * DL z (1, 0) + (X' z.1 * z.2) * DL z (0, 1) := by
  have h : ((X z.1, X' z.1 * z.2) : ℝ × ℝ)
      = X z.1 • ((1, 0) : ℝ × ℝ) + (X' z.1 * z.2) • ((0, 1) : ℝ × ℝ) := by
    simp
  rw [h, map_add, map_smul, map_smul]
  simp [mul_comm]

/-- Infinitesimal invariance of the Lagrangian under the (prolonged) symmetry, expressed as
the vanishing of the `ε`-derivative at `ε = 0` of `ε ↦ L (x + ε X x, u + ε X' x * u)`,
implies the vanishing of the directional derivative `DL z (X x, X' x * u)`. -/
