import Mathlib

/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede every other command, including the module
-- docstring above; the requested header is otherwise reproduced verbatim.)

open scoped ContDiff
open Topology

namespace Math2

/-! ## The canonical linear isometry `ℝ →L[ℝ] ℝ¹`

We realise the target Euclidean space as `EuclideanSpace ℝ (Fin N)`.  For the construction
below only `N = 1` is needed, so we set up the canonical map `ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)`
and record its basic properties. -/

/-- The canonical continuous linear map `ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)`,
sending `a` to the constant family `fun _ => a`. -/

theorem nash_embedding_surface_of_revolution {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hpos : ∀ u, 0 < h u) (hslope : ∀ u, |deriv h u| < 1) :
    ∃ (N : ℕ) (f : ℝ × ℝ → EuclideanSpace ℝ (Fin N)),
      ContDiff ℝ ∞ f ∧
      Set.InjOn f (Set.univ ×ˢ Set.Ioo 0 (2 * Real.pi)) ∧
      ∀ (x V W : ℝ × ℝ),
        inner ℝ (fderiv ℝ f x V) (fderiv ℝ f x W)
          = V.1 * W.1 + h x.1 ^ 2 * (V.2 * W.2) := by
  have hderiv : ∀ u, HasDerivAt h (deriv h u) u := fun u =>
    (hh.differentiable (by simp)).differentiableAt.hasDerivAt
  have hdsmooth : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.1 hh).2
  set q : ℝ → ℝ := fun u => 1 - deriv h u ^ 2 with hq_def
  have hqpos : ∀ u, 0 < q u := by
    intro u
    have hu := abs_lt.1 (hslope u)
    have : deriv h u ^ 2 < 1 := by nlinarith [hu.1, hu.2]
    simpa [hq_def] using this
  have hqsmooth : ContDiff ℝ ∞ q := contDiff_const.sub (hdsmooth.pow 2)
  set b : ℝ → ℝ := fun u => Real.sqrt (q u)
  have hbsmooth : ContDiff ℝ ∞ b := contDiff_sqrt_of_pos hqsmooth hqpos
  have hbpos : ∀ u, 0 < b u := fun u => Real.sqrt_pos.2 (hqpos u)
  have hbsq : ∀ u, b u * b u = 1 - deriv h u ^ 2 := fun u =>
    Real.mul_self_sqrt (hqpos u).le
  set Z : ℝ → ℝ := fun u => ∫ t in (0 : ℝ)..u, b t
  have hZ' : ∀ u, HasDerivAt Z (b u) u := fun u =>
    ((hbsmooth.continuous).integral_hasStrictDerivAt 0 u).hasDerivAt
  have hZsmooth : ContDiff ℝ ∞ Z := contDiff_of_hasDerivAt hbsmooth hZ'
  have hZmono : StrictMono Z := by
    refine strictMono_of_deriv_pos ?_
    intro u
    rw [(hZ' u).deriv]
    exact hbpos u
  -- the coordinate map into `ℝ³`
  set G : ℝ × ℝ → ℝ × ℝ × ℝ :=
    fun p => (h p.1 * Real.cos p.2, h p.1 * Real.sin p.2, Z p.1)
  have hfderiv : ∀ (x V : ℝ × ℝ), fderiv ℝ G x V
      = (deriv h x.1 * Real.cos x.2 * V.1 - h x.1 * Real.sin x.2 * V.2,
         deriv h x.1 * Real.sin x.2 * V.1 + h x.1 * Real.cos x.2 * V.2,
         b x.1 * V.1) := by
    intro x V
    have h1 : HasFDerivAt (fun p : ℝ × ℝ => h p.1) _ x :=
      (hderiv x.1).hasFDerivAt.comp x hasFDerivAt_fst
    have h2 : HasFDerivAt (fun p : ℝ × ℝ => Real.cos p.2) _ x :=
      (Real.hasDerivAt_cos x.2).hasFDerivAt.comp x hasFDerivAt_snd
    have h3 : HasFDerivAt (fun p : ℝ × ℝ => Real.sin p.2) _ x :=
      (Real.hasDerivAt_sin x.2).hasFDerivAt.comp x hasFDerivAt_snd
    have h4 : HasFDerivAt (fun p : ℝ × ℝ => Z p.1) _ x :=
      (hZ' x.1).hasFDerivAt.comp x hasFDerivAt_fst
    have hGf : HasFDerivAt G _ x := (h1.mul h2).prodMk ((h1.mul h3).prodMk h4)
    rw [hGf.fderiv]
    simp [ContinuousLinearMap.toSpanSingleton]
    refine ⟨by ring, by ring, by ring⟩
  have hGsmooth : ContDiff ℝ ∞ G :=
    ((hh.comp contDiff_fst).mul (Real.contDiff_cos.comp contDiff_snd)).prodMk
      (((hh.comp contDiff_fst).mul (Real.contDiff_sin.comp contDiff_snd)).prodMk
        (hZsmooth.comp contDiff_fst))
  refine ⟨3, fun p => space3 (G p), space3.contDiff.comp hGsmooth, ?_, ?_⟩
  · rintro p ⟨-, hp⟩ r ⟨-, hr⟩ hpr
    have hGpr : G p = G r := space3_injective hpr
    have h3 : Z p.1 = Z r.1 := congrArg (fun z : ℝ × ℝ × ℝ => z.2.2) hGpr
    have hu : p.1 = r.1 := hZmono.injective h3
    have h1 : h p.1 * Real.cos p.2 = h r.1 * Real.cos r.2 :=
      congrArg (fun z : ℝ × ℝ × ℝ => z.1) hGpr
    have h2 : h p.1 * Real.sin p.2 = h r.1 * Real.sin r.2 :=
      congrArg (fun z : ℝ × ℝ × ℝ => z.2.1) hGpr
    rw [hu] at h1 h2
    have hne : h r.1 ≠ 0 := ne_of_gt (hpos r.1)
    have hc : Real.cos p.2 = Real.cos r.2 := mul_left_cancel₀ hne h1
    have hs : Real.sin p.2 = Real.sin r.2 := mul_left_cancel₀ hne h2
    have hcos : Real.cos (p.2 - r.2) = 1 := by
      rw [Real.cos_sub, hc, hs]
      linear_combination Real.sin_sq_add_cos_sq r.2
    have hlt : p.2 - r.2 < 2 * Real.pi := by linarith [hp.2, hr.1]
    have hgt : -(2 * Real.pi) < p.2 - r.2 := by linarith [hp.1, hr.2]
    have : p.2 - r.2 = 0 := (Real.cos_eq_one_iff_of_lt_of_lt hgt hlt).1 hcos
    exact Prod.ext hu (by linarith)
  · intro x V W
    rw [show (fun p : ℝ × ℝ => space3 (G p)) = space3 ∘ G from rfl]
    have hGf : HasFDerivAt G (fderiv ℝ G x) x := by
      refine (?_ : DifferentiableAt ℝ G x).hasFDerivAt
      exact (hGsmooth.differentiable (by simp)).differentiableAt
    have : HasFDerivAt (space3 ∘ G) (space3.comp (fderiv ℝ G x)) x :=
      space3.hasFDerivAt.comp x hGf
    rw [this.fderiv]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [inner_space3, hfderiv x V, hfderiv x W]
    have hsc := Real.sin_sq_add_cos_sq x.2
    have hb := hbsq x.1
    dsimp only
    linear_combination (deriv h x.1 ^ 2 * (V.1 * W.1) + h x.1 ^ 2 * (V.2 * W.2)) * hsc
      + (V.1 * W.1) * hb

end Math2

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

