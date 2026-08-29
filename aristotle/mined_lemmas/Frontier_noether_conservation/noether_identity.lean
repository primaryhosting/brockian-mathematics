/-
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The partial derivative `∂L/∂q` of a one–dimensional Lagrangian
`L : ℝ × ℝ → ℝ` (first slot: position, second slot: velocity). -/

lemma noether_identity (L : ℝ × ℝ → ℝ) (hL : Differentiable ℝ L) (X X' : ℝ → ℝ)
    (hsym : ∀ x v : ℝ, HasDerivAt (fun s : ℝ => L (x + s * X x, v + s * (X' x * v))) 0 0)
    (x v : ℝ) :
    Lpos L x v * X x + Lvel L x v * (X' x * v) = 0 := by
  have hg : HasDerivAt (fun s : ℝ => (x + s * X x, v + s * (X' x * v)))
      ((X x, X' x * v) : ℝ × ℝ) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => x + s * X x) (X x) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (X x)).const_add x
    have h2 : HasDerivAt (fun s : ℝ => v + s * (X' x * v)) (X' x * v) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (X' x * v)).const_add v
    exact h1.prodMk h2
  have hcomp : HasDerivAt (fun s : ℝ => L (x + s * X x, v + s * (X' x * v)))
      (fderiv ℝ L (x, v) (X x, X' x * v)) 0 := by
    have hLfd : HasFDerivAt L (fderiv ℝ L (x, v))
        (x + (0 : ℝ) * X x, v + (0 : ℝ) * (X' x * v)) := by
      simpa using (hL (x, v)).hasFDerivAt
    exact hLfd.comp_hasDerivAt (0 : ℝ) hg
  have h0 : fderiv ℝ L (x, v) (X x, X' x * v) = 0 :=
    (hcomp.unique (hsym x v))
  rw [fderiv_apply_eq L] at h0
  linarith [h0]

/-- **Noether's theorem, one–dimensional case.**
Let `L : ℝ × ℝ → ℝ` be a differentiable Lagrangian, and let `X` be a smooth vector field
on configuration space generating a one–parameter family of transformations
`q ↦ q + s X(q)` under which `L` is invariant to first order (`hsym`).
If `q` is a trajectory with velocity `q'` satisfying the Euler–Lagrange equation
`d/dt (∂L/∂q̇)(q, q') = (∂L/∂q)(q, q')`, then the Noether current
`J(t) = (∂L/∂q̇)(q t, q' t) · X (q t)` is conserved. -/
