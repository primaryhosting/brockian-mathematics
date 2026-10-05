/-
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

section Goldstone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Noether / infinitesimal invariance.**  If the potential `V` is invariant under a
one-parameter family of field transformations `Φ t` whose infinitesimal generator at `t = 0`
is the continuous linear map `A`, then the gradient of `V` is everywhere orthogonal to the
direction of the symmetry flow: `dV_x (A x) = 0`. -/
theorem fderiv_apply_generator_eq_zero
    (V : E → ℝ) (hV : Differentiable ℝ V)
    (A : E →L[ℝ] E) (Φ : ℝ → E → E)
    (hΦ0 : ∀ x : E, Φ 0 x = x)
    (hinv : ∀ (t : ℝ) (x : E), V (Φ t x) = V x)
    (hgen : ∀ x : E, HasDerivAt (fun t : ℝ => Φ t x) (A x) 0) :
    ∀ x : E, fderiv ℝ V x (A x) = 0 := by
  intro x
  have h1 : HasDerivAt (fun t : ℝ => V (Φ t x)) (fderiv ℝ V x (A x)) 0 := by
    have hx : HasFDerivAt V (fderiv ℝ V x) (Φ 0 x) := by
      rw [hΦ0]
      exact (hV x).hasFDerivAt
    exact hx.comp_hasDerivAt 0 (hgen x)
  have h2 : HasDerivAt (fun t : ℝ => V (Φ t x)) 0 0 := by
    simp only [hinv]
    exact hasDerivAt_const 0 (V x)
  exact h1.unique h2

/-- **Goldstone's theorem** (finite-dimensional / classical field-theory form).

Let `V` be a `C²` potential on a real normed space `E`, invariant under a one-parameter
family of transformations `Φ t` (a continuous global symmetry) with infinitesimal generator
the continuous linear map `A`.  Let `x₀` be a vacuum, i.e. a critical point of `V`
(`fderiv ℝ V x₀ = 0`), and suppose the symmetry is *spontaneously broken* at `x₀`, meaning
that the vacuum is not invariant: `A x₀ ≠ 0`.

Then the mass matrix at the vacuum — the Hessian `fderiv ℝ (fderiv ℝ V) x₀` — annihilates the
nonzero vector `v = A x₀`.  That is, there is a massless mode: a nonzero excitation direction
with vanishing quadratic (mass) term. -/
theorem goldstone
    (V : E → ℝ) (hV : ContDiff ℝ 2 V)
    (A : E →L[ℝ] E) (Φ : ℝ → E → E)
    (hΦ0 : ∀ x : E, Φ 0 x = x)
    (hinv : ∀ (t : ℝ) (x : E), V (Φ t x) = V x)
    (hgen : ∀ x : E, HasDerivAt (fun t : ℝ => Φ t x) (A x) 0)
    (x₀ : E) (hcrit : fderiv ℝ V x₀ = 0) (hbroken : A x₀ ≠ 0) :
    ∃ v : E, v ≠ 0 ∧ ∀ w : E,
      (fderiv ℝ (fderiv ℝ V) x₀ w) v = 0 ∧ (fderiv ℝ (fderiv ℝ V) x₀ v) w = 0 := by
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  -- The first derivative map is itself differentiable.
  have hV1 : ContDiff ℝ 1 (fderiv ℝ V) := hV.fderiv_right (le_refl _)
  have hDd : Differentiable ℝ (fderiv ℝ V) := hV1.differentiable (by norm_num)
  -- Noether identity.
  have hN : ∀ x : E, fderiv ℝ V x (A x) = 0 :=
    fderiv_apply_generator_eq_zero V hVd A Φ hΦ0 hinv hgen
  -- Differentiate the Noether identity at the vacuum.
  have hg : HasFDerivAt (fun x : E => (fderiv ℝ V x) (A x))
      (((fderiv ℝ V x₀).comp (A : E →L[ℝ] E)) +
        (fderiv ℝ (fderiv ℝ V) x₀).flip (A x₀)) x₀ :=
    (hDd x₀).hasFDerivAt.clm_apply (A.hasFDerivAt)
  have hg0 : HasFDerivAt (fun _ : E => (0 : ℝ)) (0 : E →L[ℝ] ℝ) x₀ := hasFDerivAt_const 0 x₀
  have hfun : (fun x : E => (fderiv ℝ V x) (A x)) = fun _ : E => (0 : ℝ) := by
    funext x; exact hN x
  rw [hfun] at hg
  have hzero := hg.unique hg0
  have hkey : ∀ w : E, (fderiv ℝ (fderiv ℝ V) x₀ w) (A x₀) = 0 := by
    intro w
    have := congrArg (fun L : E →L[ℝ] ℝ => L w) hzero
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, hcrit] at this
    simpa using this
  -- Symmetry of the second derivative.
  have hsymm : ∀ v w : E, (fderiv ℝ (fderiv ℝ V) x₀ v) w = (fderiv ℝ (fderiv ℝ V) x₀ w) v :=
    second_derivative_symmetric (f := V) (f' := fderiv ℝ V)
      (fun y => (hVd y).hasFDerivAt) (hDd x₀).hasFDerivAt
  refine ⟨A x₀, hbroken, fun w => ⟨hkey w, ?_⟩⟩
  rw [hsymm]
  exact hkey w

end Goldstone

section MexicanHat

/-! ### A concrete instance: the Mexican-hat potential with `SO(2)` symmetry

This section checks that the hypotheses of `Phys.goldstone` are satisfiable in a
nondegenerate situation: the potential `V(x, y) = (x² + y² − 1)²` on `ℝ²`, invariant under
rotations, with the vacuum `(1, 0)`, which is not rotation invariant. -/

/-- The Mexican-hat potential `V(x, y) = (x² + y² - 1)²` on `ℝ²`. -/
noncomputable def mexicanHat : ℝ × ℝ → ℝ := fun p => (p.1 ^ 2 + p.2 ^ 2 - 1) ^ 2

/-- The rotation flow on `ℝ²`, a continuous global symmetry of `mexicanHat`. -/
noncomputable def rot : ℝ → ℝ × ℝ → ℝ × ℝ :=
  fun t p => (Real.cos t * p.1 - Real.sin t * p.2, Real.sin t * p.1 + Real.cos t * p.2)

/-- The infinitesimal generator `(x, y) ↦ (-y, x)` of the rotation flow. -/
def rotGen : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (-(ContinuousLinearMap.snd ℝ ℝ ℝ)).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)

theorem contDiff_mexicanHat : ContDiff ℝ 2 mexicanHat := by
  unfold mexicanHat; fun_prop

theorem rot_zero (p : ℝ × ℝ) : rot 0 p = p := by simp [rot]

theorem mexicanHat_rot (t : ℝ) (p : ℝ × ℝ) : mexicanHat (rot t p) = mexicanHat p := by
  have h := Real.sin_sq_add_cos_sq t
  have key : (Real.cos t * p.1 - Real.sin t * p.2) ^ 2
      + (Real.sin t * p.1 + Real.cos t * p.2) ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by nlinarith [h]
  show ((Real.cos t * p.1 - Real.sin t * p.2) ^ 2
      + (Real.sin t * p.1 + Real.cos t * p.2) ^ 2 - 1) ^ 2 = (p.1 ^ 2 + p.2 ^ 2 - 1) ^ 2
  rw [key]

theorem hasDerivAt_rot (p : ℝ × ℝ) : HasDerivAt (fun t : ℝ => rot t p) (rotGen p) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => Real.cos t * p.1 - Real.sin t * p.2) (-p.2) 0 := by
    have := ((Real.hasDerivAt_cos 0).mul_const p.1).sub ((Real.hasDerivAt_sin 0).mul_const p.2)
    simpa using this
  have h2 : HasDerivAt (fun t : ℝ => Real.sin t * p.1 + Real.cos t * p.2) p.1 0 := by
    have := ((Real.hasDerivAt_sin 0).mul_const p.1).add ((Real.hasDerivAt_cos 0).mul_const p.2)
    simpa using this
  simpa [rot, rotGen] using h1.prodMk h2

theorem fderiv_mexicanHat_vacuum : fderiv ℝ mexicanHat ((1 : ℝ), (0 : ℝ)) = 0 := by
  have hf : HasFDerivAt (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2 - 1)
      ((2 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ) + (0 : ℝ) • (ContinuousLinearMap.snd ℝ ℝ ℝ))
      ((1 : ℝ), (0 : ℝ)) := by
    have h1 : HasFDerivAt (fun p : ℝ × ℝ => p.1 ^ 2)
        ((2 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ)) ((1 : ℝ), (0 : ℝ)) := by
      have := (hasFDerivAt_fst (𝕜 := ℝ) (p := ((1 : ℝ), (0 : ℝ)))).pow 2
      simpa using this
    have h2 : HasFDerivAt (fun p : ℝ × ℝ => p.2 ^ 2)
        ((0 : ℝ) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) ((1 : ℝ), (0 : ℝ)) := by
      have := (hasFDerivAt_snd (𝕜 := ℝ) (p := ((1 : ℝ), (0 : ℝ)))).pow 2
      simpa using this
    simpa using (h1.add h2).sub_const 1
  have h3 := hf.pow 2
  have h4 : HasFDerivAt mexicanHat (0 : (ℝ × ℝ) →L[ℝ] ℝ) ((1 : ℝ), (0 : ℝ)) := by
    simpa [mexicanHat] using h3
  exact h4.fderiv

/-- The Mexican-hat potential has a massless (Goldstone) mode at the vacuum `(1, 0)`:
the rotational symmetry is spontaneously broken there, and the Hessian of the potential
annihilates the corresponding tangent direction `(0, 1)`. -/
theorem goldstone_mexicanHat :
    ∃ v : ℝ × ℝ, v ≠ 0 ∧ ∀ w : ℝ × ℝ,
      (fderiv ℝ (fderiv ℝ mexicanHat) ((1 : ℝ), (0 : ℝ)) w) v = 0 ∧
      (fderiv ℝ (fderiv ℝ mexicanHat) ((1 : ℝ), (0 : ℝ)) v) w = 0 := by
  refine goldstone mexicanHat contDiff_mexicanHat rotGen rot rot_zero
    (fun t p => mexicanHat_rot t p) hasDerivAt_rot ((1 : ℝ), (0 : ℝ)) fderiv_mexicanHat_vacuum ?_
  simp [rotGen, Prod.ext_iff]

end MexicanHat

end Phys

