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

theorem free_particle_momentum_conserved (a b : ℝ) :
    (∀ t₀ t₁ : ℝ,
        noetherCurrent (fun _ u : ℝ => u) (fun t : ℝ => a + b * t) (fun _ : ℝ => b)
            (fun _ : ℝ => 1) t₁ =
          noetherCurrent (fun _ u : ℝ => u) (fun t : ℝ => a + b * t) (fun _ : ℝ => b)
            (fun _ : ℝ => 1) t₀) ∧
      ∀ t : ℝ,
        noetherCurrent (fun _ u : ℝ => u) (fun t : ℝ => a + b * t) (fun _ : ℝ => b)
          (fun _ : ℝ => 1) t = b := by
  refine ⟨?_, by intro t; simp [noetherCurrent]⟩
  refine (noether_conservation_of_symmetry (fun _ u : ℝ => u ^ 2 / 2) (fun _ _ : ℝ => 0)
    (fun _ u : ℝ => u) (fun t : ℝ => a + b * t) (fun _ : ℝ => b) (fun _ : ℝ => 1)
    (fun _ : ℝ => 0) ?_ ?_ ?_ ?_ ?_).2
  · intro t
    simpa using ((hasDerivAt_id t).const_mul b).const_add a
  · intro x
    simpa using hasDerivAt_const x (1 : ℝ)
  · intro t
    simpa using hasDerivAt_const t b
  · intro x u
    have h : HasFDerivAt (fun p : ℝ × ℝ => p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (x, u) :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
    have hp : HasFDerivAt (fun p : ℝ × ℝ => p.2 ^ 2)
        ((2 * u) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) (x, u) := by
      simpa [nsmul_eq_mul] using h.pow 2
    have h2 : HasFDerivAt (fun p : ℝ × ℝ => p.2 ^ 2 / 2)
        (u • (ContinuousLinearMap.snd ℝ ℝ ℝ)) (x, u) := by
      simpa [smul_smul, Pi.smul_def, smul_eq_mul, div_eq_inv_mul, mul_comm, mul_assoc,
        mul_left_comm] using hp.const_smul ((2 : ℝ)⁻¹)
    have hclm :
        ((0 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ) + u • (ContinuousLinearMap.snd ℝ ℝ ℝ)) =
          u • (ContinuousLinearMap.snd ℝ ℝ ℝ) := by
      ext <;> simp
    simpa [hclm] using h2
  · intro s x u
    simp

end Frontier

