import Mathlib
/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- **Goldstone's theorem** (classical field-theory / mechanical form).

Setting: `V : E → ℝ` is a potential on a real normed space `E`, invariant under a
one-parameter family `g : ℝ → (E ≃L[ℝ] E)` of continuous linear symmetries
(`hinv : ∀ t x, V (g t x) = V x`).  The vacuum `v` minimises `V` (`hmin`).
The symmetry is *spontaneously broken*: the orbit `t ↦ g t v` of the vacuum moves,
i.e. it has a nonzero velocity `w ≠ 0` at `t = 0`.

Conclusion: the mass matrix, i.e. the Hessian `fderiv ℝ (fderiv ℝ V) v` of the potential
at the vacuum, annihilates the nonzero vector `w`.  Thus there is a massless mode
(a Goldstone boson): a nonzero fluctuation direction with vanishing mass term. -/
theorem goldstone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → ℝ) (v w : E) (g : ℝ → (E ≃L[ℝ] E))
    (hV : Differentiable ℝ V)
    (hmin : ∀ x, V v ≤ V x)
    (hinv : ∀ t x, V (g t x) = V x)
    (hHess : DifferentiableAt ℝ (fun x => fderiv ℝ V x) v)
    (hg0 : (g 0 : E → E) v = v)
    (horbit : HasDerivAt (fun t => (g t : E → E) v) w 0)
    (hbreak : w ≠ 0) :
    ∃ w : E, w ≠ 0 ∧ fderiv ℝ (fun x => fderiv ℝ V x) v w = 0 := by
  refine ⟨w, hbreak, ?_⟩
  -- The vacuum is a critical point.
  have hcrit : fderiv ℝ V v = 0 := by
    have : IsLocalMin V v := Filter.Eventually.of_forall hmin
    exact this.fderiv_eq_zero
  -- Every point of the vacuum orbit is a critical point.
  have horbit_crit : ∀ t, fderiv ℝ V ((g t : E → E) v) = 0 := by
    intro t
    have h1 : HasFDerivAt (fun x => V ((g t : E → E) x))
        ((fderiv ℝ V ((g t : E → E) v)).comp ((g t : E →L[ℝ] E))) v :=
      (hV ((g t : E → E) v)).hasFDerivAt.comp v
        ((g t : E →L[ℝ] E)).hasFDerivAt
    have h2 : HasFDerivAt (fun x => V ((g t : E → E) x)) (fderiv ℝ V v) v := by
      simpa [funext (hinv t)] using (hV v).hasFDerivAt
    have h3 : (fderiv ℝ V ((g t : E → E) v)).comp ((g t : E →L[ℝ] E)) = 0 := by
      rw [h1.unique h2, hcrit]
    ext y
    have := congrArg (fun L : E →L[ℝ] ℝ => L ((g t).symm y)) h3
    simpa using this
  -- Differentiating the orbit of critical points at `t = 0` kills `w`.
  have hAt : HasFDerivAt (fun x => fderiv ℝ V x)
      (fderiv ℝ (fun x => fderiv ℝ V x) v) ((g 0 : E → E) v) := by
    rw [hg0]; exact hHess.hasFDerivAt
  have hcomp : HasDerivAt (fun t => fderiv ℝ V ((g t : E → E) v))
      ((fderiv ℝ (fun x => fderiv ℝ V x) v) w) 0 :=
    hAt.comp_hasDerivAt (0 : ℝ) horbit
  have hzero : HasDerivAt (fun t => fderiv ℝ V ((g t : E → E) v)) 0 0 := by
    simpa [funext horbit_crit] using (hasDerivAt_const (0 : ℝ) (0 : E →L[ℝ] ℝ))
  exact hcomp.unique hzero

/-! ## A concrete instance: the Mexican-hat potential on `ℂ`

The hypotheses of `Phys.goldstone` are non-vacuous: they are satisfied by the
Mexican-hat potential `V z = (‖z‖ ^ 2 - 1) ^ 2` on `ℂ ≃ ℝ²`, invariant under the
circle group of rotations, with vacuum `v = 1`, whose orbit velocity is `i ≠ 0`. -/

/-- The Mexican-hat (wine-bottle) potential on `ℂ`. -/
noncomputable def mexicanHat : ℂ → ℝ := fun z => (‖z‖ ^ 2 - 1) ^ 2

/-- The one-parameter rotation group acting on `ℂ`. -/
noncomputable def rot (t : ℝ) : ℂ ≃L[ℝ] ℂ :=
  (rotation (Circle.exp t)).toContinuousLinearEquiv

lemma rot_apply (t : ℝ) (x : ℂ) :
    (rot t : ℂ → ℂ) x = Complex.exp ((t : ℂ) * Complex.I) * x := by
  simp only [rot, LinearIsometryEquiv.coe_toContinuousLinearEquiv, rotation_apply,
    Circle.coe_exp]

lemma contDiff_mexicanHat : ContDiff ℝ 2 mexicanHat := by
  have h : ContDiff ℝ 2 (fun z : ℂ => ‖z‖ ^ 2) := by
    have : (fun z : ℂ => ‖z‖ ^ 2) = fun z : ℂ => z.re ^ 2 + z.im ^ 2 := by
      funext z
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rw [this]
    exact (Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2)
  exact (h.sub contDiff_const).pow 2

/-- Goldstone's theorem applied to the Mexican-hat potential: the mass matrix at the
vacuum `v = 1` has a nonzero null vector, i.e. there is a massless mode. -/
theorem goldstone_mexicanHat :
    ∃ w : ℂ, w ≠ 0 ∧ fderiv ℝ (fun x => fderiv ℝ mexicanHat x) 1 w = 0 := by
  refine goldstone mexicanHat 1 Complex.I rot
    (contDiff_mexicanHat.differentiable (by norm_num)) ?_ ?_ ?_ ?_ ?_ Complex.I_ne_zero
  · intro x
    have h1 : mexicanHat 1 = 0 := by norm_num [mexicanHat]
    rw [h1]
    simp only [mexicanHat]
    positivity
  · intro t x
    have h2 : ‖(rot t : ℂ → ℂ) x‖ = ‖x‖ := (rotation (Circle.exp t)).norm_map x
    simp only [mexicanHat, h2]
  · exact ((contDiff_mexicanHat.fderiv_right (m := 1) le_rfl).differentiable
      (by norm_num)) 1
  · rw [rot_apply]; norm_num
  · have h : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I
    have heq : (fun t : ℝ => (rot t : ℂ → ℂ) 1)
        = fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) := by
      funext t; rw [rot_apply, mul_one]
    rw [heq]
    simpa using h.cexp

end Phys

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

