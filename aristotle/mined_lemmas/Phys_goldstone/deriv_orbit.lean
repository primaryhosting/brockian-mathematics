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

lemma deriv_orbit (R : ℝ → (E →L[ℝ] E)) (hR : ContDiff ℝ 2 (fun t => R t))
    (hgroup : ∀ s t, R (s + t) = (R s).comp (R t)) (v : E) (s : ℝ) :
    deriv (fun t => R t v) s = R s (deriv (fun t => R t v) 0) := by
  set γ : ℝ → E := fun t => R t v with hγdef
  have hγC : ContDiff ℝ 2 γ := (ContinuousLinearMap.apply ℝ E v).contDiff.comp hR
  have hshift : (fun h => γ (s + h)) = fun h => R s (γ h) := by
    funext h
    simp [hγdef, hgroup s h]
  have h1 : HasDerivAt (fun h => γ (s + h)) (deriv γ s) 0 := by
    have hs : HasDerivAt γ (deriv γ s) (s + 0) := by
      rw [add_zero]
      exact (hγC.differentiable (by norm_num) s).hasDerivAt
    exact hs.comp_const_add s 0
  have h2 : HasDerivAt (fun h => R s (γ h)) (R s (deriv γ 0)) 0 :=
    (R s).hasFDerivAt.comp_hasDerivAt 0 ((hγC.differentiable (by norm_num) 0).hasDerivAt)
  rw [hshift] at h1
  exact h1.unique h2

/-- **Goldstone's theorem.**

Let `V : E → ℝ` be a `C²` potential on a real normed space `E` (the space of field values),
invariant under a continuous (`C²`) one-parameter group of global symmetries
`R : ℝ → (E →L[ℝ] E)`, i.e. `V (R t x) = V x` for all `t` and `x`.  Let `v` be a vacuum,
i.e. a local minimum of `V`, and suppose the symmetry is *spontaneously broken* at `v`,
i.e. `v` is not invariant: `R t v ≠ v` for some `t`.

Then the mass form (Hessian) of `V` at `v` has a nontrivial kernel: there is a nonzero
direction `X` with `massForm V v X = 0`, i.e. a massless mode — a Goldstone boson. -/
