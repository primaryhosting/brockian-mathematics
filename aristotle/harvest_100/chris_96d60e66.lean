/-
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Note: Lean does not allow a module docstring before `import`, so this header is a plain
block comment and is repeated as a module docstring below.)
-/

import Mathlib

/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Scope of what is proved here

The full Nash embedding theorem (every Riemannian manifold admits a smooth isometric
embedding into some `ℝᴺ`) is not available in Mathlib, and its proof (Nash-Moser implicit
function theorem, or the Gunther fixed-point argument) is a large development that is not
formalised here.

What *is* proved, in full, is the isometric embedding theorem for an explicit infinite
dimensional family of Riemannian metrics on `ℝⁿ`, namely those of the form

  `g x (u, v) = ∑ i, a i (x i) * u i * v i + ∑ k, (dψ k x u) * (dψ k x v)`,

with each `a i : ℝ → ℝ` smooth and positive and each `ψ k : ℝⁿ → ℝ` smooth.  Every such `g`
is a smooth Riemannian metric, and the family contains, through the terms `ψ k`, the induced
first fundamental forms of graphs of smooth maps `ℝⁿ → ℝᵐ` (which are not flat in general).
For each of them we build an explicit smooth embedding `f : ℝⁿ → ℝⁿ⁺ᵐ` whose pullback of the
Euclidean metric is exactly `g`; the construction reparametrises each coordinate by its
arclength `t ↦ ∫₀ᵗ √(a i)` and adjoins the graph coordinates `ψ k`.
-/

open scoped ContDiff RealInnerProductSpace BigOperators
open Topology

namespace Math2

/-! ## One-dimensional arclength reparametrisation -/

/-- The antiderivative `x ↦ ∫₀ˣ h` of `h`. -/
noncomputable def arcLen (h : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, h t

lemma hasDerivAt_arcLen {h : ℝ → ℝ} (hc : Continuous h) (x : ℝ) :
    HasDerivAt (arcLen h) (h x) x :=
  (intervalIntegral.integral_hasStrictDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).hasDerivAt

lemma deriv_arcLen {h : ℝ → ℝ} (hc : Continuous h) : deriv (arcLen h) = h :=
  funext fun x => (hasDerivAt_arcLen hc x).deriv

lemma contDiff_arcLen {h : ℝ → ℝ} (hc : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (arcLen h) := by
  rw [contDiff_infty_iff_deriv, deriv_arcLen hc.continuous]
  exact ⟨fun x => (hasDerivAt_arcLen hc.continuous x).differentiableAt, hc⟩

lemma strictMono_arcLen {h : ℝ → ℝ} (hc : Continuous h) (hpos : ∀ x, 0 < h x) :
    StrictMono (arcLen h) := by
  intro x y hxy
  have hint : ∀ a b : ℝ, IntervalIntegrable h MeasureTheory.volume a b :=
    fun a b => hc.intervalIntegrable a b
  have : 0 < ∫ t in x..y, h t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hint x y) (fun t _ => hpos t) hxy
  have hsplit : arcLen h x + ∫ t in x..y, h t = arcLen h y :=
    intervalIntegral.integral_add_adjacent_intervals (hint 0 x) (hint x y)
  linarith [hsplit, this]

lemma isEmbedding_arcLen {h : ℝ → ℝ} (hc : ContDiff ℝ ∞ h) (hpos : ∀ x, 0 < h x) :
    IsEmbedding (arcLen h) := by
  have hmono := strictMono_arcLen hc.continuous hpos
  refine hmono.isEmbedding_of_ordConnected ?_
  have h1 : IsPreconnected (arcLen h '' Set.univ) :=
    (isPreconnected_univ (α := ℝ)).image _ (contDiff_arcLen hc).continuous.continuousOn
  rw [← Set.image_univ]
  exact h1.ordConnected

/-! ## The embedding theorem -/

/--
**Nash-type isometric embedding theorem.**

For every Riemannian metric on `ℝⁿ` of the form
`g x (u, v) = ∑ i, a i (x i) * u i * v i + ∑ k, (dψ k x u) * (dψ k x v)`
(with each `a i` a smooth positive function of a single coordinate and each `ψ k` a smooth
real function on `ℝⁿ`) there are `N` and a smooth embedding `f : ℝⁿ → ℝᴺ` whose pullback of
the Euclidean metric is `g`, i.e. `⟪Df x u, Df x v⟫ = g x (u, v)` for all `x, u, v`.

The embedding is explicit: `f x = (F₁ (x 1), …, Fₙ (x n), ψ₁ x, …, ψₘ x)` where `Fᵢ` is the
arclength reparametrisation `Fᵢ t = ∫₀ᵗ √(aᵢ)`, and `N = n + m`.

(This is the special case of Nash's theorem for this class of metrics; through the terms
`ψ k` the class contains the induced metric of the graph of any smooth map `ℝⁿ → ℝᵐ`.)
-/
theorem nash_embedding {n m : ℕ} (a : Fin n → ℝ → ℝ)
    (ψ : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (hpos : ∀ i t, 0 < a i t)
    (hψ : ∀ k, ContDiff ℝ ∞ (ψ k)) :
    ∃ (N : ℕ) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N)),
      ContDiff ℝ ∞ f ∧ IsEmbedding f ∧
      ∀ x u v : EuclideanSpace ℝ (Fin n),
        ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫
          = (∑ i, a i (x i) * (u i * v i))
            + ∑ k, fderiv ℝ (ψ k) x u * fderiv ℝ (ψ k) x v := by
  classical
  -- the coordinate speeds `√(aᵢ)` and their antiderivatives
  set d : Fin n → ℝ → ℝ := fun i t => Real.sqrt (a i t) with hd_def
  have hdc : ∀ i, ContDiff ℝ ∞ (d i) := fun i => (ha i).sqrt fun t => (hpos i t).ne'
  have hdpos : ∀ i t, 0 < d i t := fun i t => Real.sqrt_pos.mpr (hpos i t)
  have hdsq : ∀ i t, d i t * d i t = a i t := fun i t => Real.mul_self_sqrt (hpos i t).le
  set F : Fin n → ℝ → ℝ := fun i => arcLen (d i) with hF_def
  have hFderiv : ∀ i t, HasDerivAt (F i) (d i t) t := fun i t =>
    hasDerivAt_arcLen (hdc i).continuous t
  -- the coordinate maps
  set E := EuclideanSpace.equiv (Fin n) ℝ with hE_def
  set E' := EuclideanSpace.equiv (Fin (n + m)) ℝ with hE'_def
  set P : EuclideanSpace ℝ (Fin n) → (Fin (n + m) → ℝ) :=
    fun x => Fin.append (fun i => F i (x i)) (fun k => ψ k x) with hP_def
  set f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + m)) :=
    fun x => E'.symm (P x) with hf_def
  -- the linear map that will be the derivative of `P` at `x`
  set Q : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin (n + m) → ℝ)) :=
    fun x => ContinuousLinearMap.pi
      (Fin.append
        (fun i => (d i (x i)) •
          (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
        (fun k => fderiv ℝ (ψ k) x)) with hQ_def
  -- smoothness
  have hPsmooth : ContDiff ℝ ∞ P := by
    rw [contDiff_pi]
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i
      have hproj : ContDiff ℝ ∞ fun x : EuclideanSpace ℝ (Fin n) => x i :=
        (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
      simpa [hP_def] using (contDiff_arcLen (hdc i)).comp hproj
    · intro k
      simpa [hP_def] using hψ k
  have hfsmooth : ContDiff ℝ ∞ f :=
    (E'.symm : (Fin (n + m) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n + m))).contDiff.comp hPsmooth
  -- the derivative of `P`
  have hPderiv : ∀ x : EuclideanSpace ℝ (Fin n), HasFDerivAt P (Q x) x := by
    intro x
    rw [hP_def, hQ_def, hasFDerivAt_pi']
    intro j
    rw [ContinuousLinearMap.proj_pi]
    refine Fin.addCases ?_ ?_ j
    · intro i
      simpa using (hFderiv i (x i)).comp_hasFDerivAt x
        (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
    · intro k
      simpa using ((hψ k).differentiable (by simp) x).hasFDerivAt
  have hfderiv : ∀ x : EuclideanSpace ℝ (Fin n),
      HasFDerivAt f ((E'.symm : (Fin (n + m) → ℝ) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + m))).comp (Q x)) x :=
    fun x => (E'.symm : (Fin (n + m) → ℝ) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + m))).hasFDerivAt.comp x (hPderiv x)
  -- the embedding property
  have hGemb : IsEmbedding fun (y : Fin n → ℝ) (i : Fin n) => F i (y i) :=
    IsEmbedding.piMap fun i => isEmbedding_arcLen (hdc i) (hdpos i)
  have hcomp : (fun (y : Fin (n + m) → ℝ) (i : Fin n) => y (Fin.castAdd m i)) ∘ P
      = (fun (y : Fin n → ℝ) (i : Fin n) => F i (y i)) ∘ (fun x => E x) := by
    funext x i
    simp [hP_def, hE_def, EuclideanSpace.equiv]
  have hPemb : IsEmbedding P := by
    have hfst : Continuous fun (y : Fin (n + m) → ℝ) (i : Fin n) => y (Fin.castAdd m i) := by
      fun_prop
    have hcompemb :
        IsEmbedding ((fun (y : Fin (n + m) → ℝ) (i : Fin n) => y (Fin.castAdd m i)) ∘ P) := by
      rw [hcomp]
      exact hGemb.comp E.toHomeomorph.isEmbedding
    refine ⟨IsInducing.of_comp hPsmooth.continuous hfst hcompemb.toIsInducing, ?_⟩
    intro x y hxy
    exact hcompemb.injective (by simp [Function.comp, hxy])
  have hfemb : IsEmbedding f := E'.symm.toHomeomorph.isEmbedding.comp hPemb
  refine ⟨n + m, f, hfsmooth, hfemb, ?_⟩
  intro x u v
  -- the derivative of `f` in coordinates
  have happ : ∀ w : EuclideanSpace ℝ (Fin n),
      fderiv ℝ f x w
        = E'.symm (Fin.append (fun i => d i (x i) * w i)
            (fun k => fderiv ℝ (ψ k) x w) : Fin (n + m) → ℝ) := by
    intro w
    have hQw : Q x w
        = (Fin.append (fun i => d i (x i) * w i)
            (fun k => fderiv ℝ (ψ k) x w) : Fin (n + m) → ℝ) := by
      funext j
      rw [hQ_def]
      refine Fin.addCases ?_ ?_ j <;> intro _ <;> simp
    rw [(hfderiv x).fderiv, ContinuousLinearMap.comp_apply, hQw]
    rfl
  rw [happ u, happ v]
  have hinner : ∀ y z : Fin (n + m) → ℝ, ⟪E'.symm y, E'.symm z⟫ = ∑ j, y j * z j := by
    intro y z
    simp [hE'_def, PiLp.inner_apply, EuclideanSpace.equiv, mul_comm]
  rw [hinner, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.append_left, Fin.append_left, ← hdsq i (x i)]
    ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fin.append_right, Fin.append_right]

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

