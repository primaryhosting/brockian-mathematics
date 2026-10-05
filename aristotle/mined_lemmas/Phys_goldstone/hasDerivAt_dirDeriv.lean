import Mathlib

/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede any module docstring, so the required
header comment appears immediately after the single `import Mathlib` line.)

## Statement

Spontaneous breaking of a continuous global symmetry yields a massless mode (Goldstone).

We work with a scalar potential `V : E → ℝ` on a real normed space `E` of field values,
assumed `C²`.  A *vacuum* is a local minimum `v` of `V`.  The *mass form* at `v` is the
Hessian `massForm V v = D²V(v)`, whose matrix in an orthonormal basis is the mass matrix
`M_{ij} = ∂_i∂_j V(v)` of the quadratic fluctuations around `v`; a nonzero vector in its
kernel is a zero-eigenvalue direction, i.e. a **massless mode**.

A *continuous global symmetry* is a smooth one-parameter group `R : ℝ → (E →L[ℝ] E)`
(`R (s+t) = R s ∘ R t`, `R 0 = id`) of linear transformations of the field values leaving
the potential invariant: `V (R t x) = V x`.  It is *spontaneously broken* at the vacuum `v`
when `v` itself is not invariant, i.e. `R t v ≠ v` for some `t`.

`Phys.goldstone` then produces a nonzero `X` in the kernel of the mass form.
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

open Set Filter Topology

namespace Phys

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **mass form** (Hessian of the potential) of a scalar potential `V` at a
configuration `v`.  In finite dimensions, in an orthonormal basis, this is the mass matrix
`M_{ij} = ∂_i ∂_j V (v)` of the small fluctuations around `v`; a nonzero vector in its
kernel is a **massless mode**. -/

lemma hasDerivAt_dirDeriv (V : E → ℝ) (hV : ContDiff ℝ 2 V)
    (γ : ℝ → E) (hγ : ContDiff ℝ 2 γ) (t : ℝ) :
    HasDerivAt (fun s => fderiv ℝ V (γ s) (deriv γ s))
      (massForm V (γ t) (deriv γ t) (deriv γ t)
        + fderiv ℝ V (γ t) (deriv (deriv γ) t)) t := by
  have hc : HasDerivAt (fun s => fderiv ℝ V (γ s)) (massForm V (γ t) (deriv γ t)) t :=
    (hasFDerivAt_massForm V hV (γ t)).comp_hasDerivAt t
      ((hγ.differentiable (by norm_num) t).hasDerivAt)
  have h2 : ContDiff ℝ (1 + 1) γ := by norm_num; exact hγ
  have hu : HasDerivAt (deriv γ) (deriv (deriv γ) t) t :=
    ((h2.deriv'.differentiable (by norm_num)) t).hasDerivAt
  exact hc.clm_apply hu

/-- One-dimensional second derivative test: the second derivative of a real function at a
local minimum is nonnegative. -/
