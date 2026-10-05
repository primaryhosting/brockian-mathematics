import Mathlib

/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
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

namespace Phys

section Goldstone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The mass (Hessian) matrix of a potential `V` at a point `v`: the second Fréchet
derivative of `V`, viewed as a bilinear form `E → E → ℝ`. -/
noncomputable def massMatrix (V : E → ℝ) (v : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun x => fderiv ℝ V x) v

/-- **Infinitesimal invariance.** If a one–parameter family of transformations `g t`
leaves the potential `V` invariant, and its generator at `t = 0` is the linear map `T`,
then the gradient of `V` at any point `x` annihilates the symmetry direction `T x`. -/
theorem fderiv_apply_generator_eq_zero
    (V : E → ℝ) (g : ℝ → E → E) (T : E →L[ℝ] E)
    (hV : Differentiable ℝ V)
    (hg0 : ∀ x, g 0 x = x)
    (hgT : ∀ x, HasDerivAt (fun t => g t x) (T x) 0)
    (hsym : ∀ t x, V (g t x) = V x) (x : E) :
    fderiv ℝ V x (T x) = 0 := by
  have hVx : HasFDerivAt V (fderiv ℝ V x) ((fun t => g t x) 0) := by
    rw [hg0 x]; exact (hV x).hasFDerivAt
  have hcomp : HasDerivAt (fun t => V (g t x)) (fderiv ℝ V x (T x)) 0 :=
    hVx.comp_hasDerivAt 0 (hgT x)
  have hconst : HasDerivAt (fun t : ℝ => V (g t x)) 0 0 := by
    simpa only [hsym] using (hasDerivAt_const (0 : ℝ) (V x))
  exact hcomp.unique hconst

/-- **Goldstone's theorem** (classical / tree-level form).

Let `V : E → ℝ` be a twice continuously differentiable potential on a real normed space,
invariant under a one–parameter group of transformations `g t` whose generator at `t = 0`
is the continuous linear map `T` (i.e. `g 0 = id` and `(d/dt) g t x |_{t=0} = T x`).
Let `v` be a vacuum, i.e. a local minimum of `V`. If the symmetry is *spontaneously
broken* at `v`, meaning that `v` is not invariant under the symmetry to first order
(`T v ≠ 0`), then the mass matrix (Hessian) of `V` at `v` has a nontrivial kernel:
the direction `w = T v` is a massless mode. -/
theorem goldstone
    (V : E → ℝ) (g : ℝ → E → E) (T : E →L[ℝ] E) (v : E)
    (hV : ContDiff ℝ 2 V)
    (hg0 : ∀ x, g 0 x = x)
    (hgT : ∀ x, HasDerivAt (fun t => g t x) (T x) 0)
    (hsym : ∀ t x, V (g t x) = V x)
    (hmin : IsLocalMin V v)
    (hbroken : T v ≠ 0) :
    ∃ w : E, w ≠ 0 ∧ ∀ u : E, massMatrix V v u w = 0 := by
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  -- infinitesimal invariance
  have hinv : ∀ x, fderiv ℝ V x (T x) = 0 :=
    fderiv_apply_generator_eq_zero V g T hVd hg0 hgT hsym
  -- `v` is a stationary point of `V`
  have hstat : fderiv ℝ V v = 0 := hmin.fderiv_eq_zero
  -- the derivative map `x ↦ fderiv ℝ V x` is differentiable
  have hfd : Differentiable ℝ (fun x => fderiv ℝ V x) :=
    (hV.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl
  have hc : HasFDerivAt (fun x => fderiv ℝ V x) (massMatrix V v) v := (hfd v).hasFDerivAt
  have hu : HasFDerivAt (fun x => T x) T v := T.hasFDerivAt
  have hprod : HasFDerivAt (fun y => fderiv ℝ V y (T y))
      (((fderiv ℝ V v).comp T) + (massMatrix V v).flip (T v)) v := hc.clm_apply hu
  have hzero : HasFDerivAt (fun y : E => fderiv ℝ V y (T y)) 0 v := by
    simpa only [hinv] using (hasFDerivAt_const (0 : ℝ) v)
  have hD := hprod.unique hzero
  refine ⟨T v, hbroken, fun u => ?_⟩
  have := congrArg (fun L : E →L[ℝ] ℝ => L u) hD
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, hstat, ContinuousLinearMap.zero_apply] at this
  simpa using this

end Goldstone

end Phys

