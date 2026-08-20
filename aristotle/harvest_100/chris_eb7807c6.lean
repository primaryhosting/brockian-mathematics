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
noncomputable def line : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (EuclideanSpace.equiv (Fin 1) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.id ℝ ℝ)

@[simp] lemma line_apply (a : ℝ) (i : Fin 1) : line a i = a := by simp [line]

lemma inner_line (a b : ℝ) : inner ℝ (line a) (line b) = a * b := by
  simp [PiLp.inner_apply, mul_comm]

lemma norm_line (a : ℝ) : ‖line a‖ = ‖a‖ := by
  simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]

lemma isometry_line : Isometry line :=
  AddMonoidHomClass.isometry_of_norm line norm_line

/-! ## Auxiliary analytic facts -/

/-- The pointwise square root of a smooth positive function is smooth. -/
lemma contDiff_sqrt_of_pos {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hpos : ∀ x, 0 < g x) :
    ContDiff ℝ ∞ fun x => Real.sqrt (g x) := by
  rw [contDiff_iff_contDiffAt]
  exact fun x => hg.contDiffAt.sqrt (ne_of_gt (hpos x))

/-- A function whose derivative everywhere equals a smooth function is smooth. -/
lemma contDiff_of_hasDerivAt {F a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (h : ∀ x, HasDerivAt F (a x) x) : ContDiff ℝ ∞ F := by
  have hd : deriv F = a := funext fun x => (h x).deriv
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun x => (h x).differentiableAt, by rw [hd]; exact ha⟩

/-- A continuous strictly monotone function `ℝ → ℝ` is a topological embedding. -/
lemma isEmbedding_of_strictMono {F : ℝ → ℝ} (hF : Continuous F) (hm : StrictMono F) :
    IsEmbedding F := by
  refine hm.isEmbedding_of_ordConnected ?_
  have : IsPreconnected (Set.range F) := by
    rw [← Set.image_univ]
    exact isPreconnected_univ.image F hF.continuousOn
  exact this.ordConnected

/-! ## The Nash embedding theorem in dimension one

Mathlib does not contain the Nash embedding theorem (nor, at present, any of the hard
implicit-function-theorem machinery used in its proof), so nothing in the library closes the
general statement.  What we prove here is the one–dimensional case, which is a genuine
(non-vacuous, non-circular) instance of the theorem: *an arbitrary* smooth Riemannian metric on
the one–dimensional manifold `ℝ` is realised as the metric induced by a smooth embedding into a
Euclidean space `ℝ^N`.

A Riemannian metric on the manifold `ℝ` is a smooth positive function `g`, the associated inner
product on the tangent space `T_x ℝ ≃ ℝ` being `(v, w) ↦ g x * (v * w)`.  A map
`f : ℝ → EuclideanSpace ℝ (Fin N)` is an isometric immersion when its differential pulls the
Euclidean inner product back to this metric, i.e.
`⟪Df_x v, Df_x w⟫ = g x * (v * w)`; it is an isometric *embedding* when moreover it is a
topological embedding.

The embedding is the arclength map `x ↦ ∫ t in 0..x, √(g t)` into `ℝ^1`. -/

/-- **Nash embedding theorem, one-dimensional case.**
Every Riemannian metric `g` on the one-dimensional manifold `ℝ` (a smooth, everywhere positive
function, giving the tangent space at `x` the inner product `(v, w) ↦ g x * (v * w)`) is induced
by a smooth isometric embedding of `ℝ` into some Euclidean space `ℝ^N`: there is `N` and a
smooth topological embedding `f : ℝ → EuclideanSpace ℝ (Fin N)` whose differential pulls the
Euclidean inner product back to `g`. -/
theorem nash_embedding {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hpos : ∀ x, 0 < g x) :
    ∃ (N : ℕ) (f : ℝ → EuclideanSpace ℝ (Fin N)),
      ContDiff ℝ ∞ f ∧ IsEmbedding f ∧
      ∀ x v w : ℝ, inner ℝ (fderiv ℝ f x v) (fderiv ℝ f x w) = g x * (v * w) := by
  set a : ℝ → ℝ := fun x => Real.sqrt (g x)
  have ha : ContDiff ℝ ∞ a := contDiff_sqrt_of_pos hg hpos
  have hapos : ∀ x, 0 < a x := fun x => Real.sqrt_pos.2 (hpos x)
  have hasq : ∀ x, a x * a x = g x := fun x =>
    Real.mul_self_sqrt (hpos x).le
  set F : ℝ → ℝ := fun u => ∫ t in (0 : ℝ)..u, a t
  have hF' : ∀ x, HasDerivAt F (a x) x := fun x =>
    ((ha.continuous).integral_hasStrictDerivAt 0 x).hasDerivAt
  have hFsmooth : ContDiff ℝ ∞ F := contDiff_of_hasDerivAt ha hF'
  have hFmono : StrictMono F := by
    refine strictMono_of_deriv_pos ?_
    intro x
    rw [(hF' x).deriv]
    exact hapos x
  refine ⟨1, fun x => line (F x), ?_, ?_, ?_⟩
  · exact line.contDiff.comp hFsmooth
  · exact isometry_line.isEmbedding.comp
      (isEmbedding_of_strictMono hFsmooth.continuous hFmono)
  · intro x v w
    have hfd : HasFDerivAt (fun x => line (F x))
        (line.comp (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (a x))) x :=
      line.hasFDerivAt.comp x (hF' x).hasFDerivAt
    rw [hfd.fderiv]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
    rw [inner_line]
    rw [← hasq x]
    ring

/-! ## A curved two-dimensional case: surfaces of revolution

The one-dimensional case above concerns only flat metrics.  We also treat a genuinely curved
family: the rotationally symmetric metrics `du² + h(u)² dv²` on `ℝ²` (whose Gauss curvature is
`-h''/h`, so generically nonzero).  Under the classical condition `|h'| < 1`, such a metric is
induced by the smooth map
`(u, v) ↦ (h u * cos v, h u * sin v, ∫ t in 0..u, √(1 - h' t ^ 2))` into `ℝ³`,
which is injective on the strip `ℝ × (0, 2π)`. -/

/-- The canonical continuous linear map `ℝ³ →L[ℝ] EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def space3 : (ℝ × ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ),
      (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)),
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))])

@[simp] lemma space3_apply_zero (a : ℝ × ℝ × ℝ) : space3 a 0 = a.1 := by simp [space3]
@[simp] lemma space3_apply_one (a : ℝ × ℝ × ℝ) : space3 a 1 = a.2.1 := by simp [space3]
@[simp] lemma space3_apply_two (a : ℝ × ℝ × ℝ) : space3 a 2 = a.2.2 := by simp [space3]

lemma inner_space3 (a b : ℝ × ℝ × ℝ) :
    inner ℝ (space3 a) (space3 b) = a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2 := by
  simp [PiLp.inner_apply, space3, Fin.sum_univ_three, mul_comm]

lemma space3_injective : Function.Injective space3 := by
  intro a b hab
  have h0 : space3 a 0 = space3 b 0 := by rw [hab]
  have h1 : space3 a 1 = space3 b 1 := by rw [hab]
  have h2 : space3 a 2 = space3 b 2 := by rw [hab]
  simp only [space3_apply_zero, space3_apply_one, space3_apply_two] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

/-- **Nash embedding for rotationally symmetric surfaces.**
Let `h : ℝ → ℝ` be smooth, positive, with `|h'| < 1`.  Then the (generally curved) Riemannian
metric `du² + h(u)² dv²` on `ℝ²` is induced by a smooth map into a Euclidean space `ℝ^N`
which is injective on the strip `ℝ × (0, 2π)` (on all of `ℝ²` the map is only an immersion,
because the metric is `2π`-periodic in `v`). -/
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

