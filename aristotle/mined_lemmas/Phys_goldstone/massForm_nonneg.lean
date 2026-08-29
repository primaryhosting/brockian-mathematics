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

lemma massForm_nonneg (V : E → ℝ) (hV : ContDiff ℝ 2 V) {v : E} (hmin : IsLocalMin V v)
    (w : E) : 0 ≤ massForm V v w w := by
  set γ : ℝ → E := fun s => v + s • w with hγdef
  have hγC : ContDiff ℝ 2 γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hd : ∀ t : ℝ, HasDerivAt γ w t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => s • w) w t := by
      simpa using (hasDerivAt_id t).smul_const w
    exact h1.const_add v
  have hderiv : deriv γ = fun _ : ℝ => w := funext fun t => (hd t).deriv
  have hderiv2 : deriv (deriv γ) = fun _ : ℝ => (0 : E) := by
    rw [hderiv]; exact funext fun t => deriv_const t w
  have hγ0 : γ 0 = v := by simp [hγdef]
  have hf : ∀ t : ℝ, HasDerivAt (fun s => V (γ s)) (fderiv ℝ V (γ t) w) t := fun t =>
    ((hV.differentiable (by norm_num) (γ t)).hasFDerivAt).comp_hasDerivAt t (hd t)
  have hminV : IsLocalMin V (γ 0) := by rw [hγ0]; exact hmin
  have hmin0 : IsLocalMin (fun s => V (γ s)) 0 :=
    hminV.comp_continuous hγC.continuous.continuousAt
  have hg := hasDerivAt_dirDeriv V hV γ hγC 0
  rw [hderiv2, hderiv, hγ0] at hg
  simp only [map_zero, add_zero] at hg
  exact second_deriv_nonneg_of_isLocalMin hf hmin0 hg

/-- A vector on which a positive semidefinite symmetric bilinear form vanishes lies in the
kernel of the form (Cauchy–Schwarz). -/
