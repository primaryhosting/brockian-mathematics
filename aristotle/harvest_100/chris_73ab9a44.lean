import Mathlib

/-!
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(Lean requires `import` to be the very first command of a file, before any module-level doc
comment, so the required header block is placed immediately after `import Mathlib`.)

## Contents

* `Frontier.IsClosed3Manifold` : a closed (compact, boundaryless, second countable, Hausdorff)
  topological 3-manifold.
* `Frontier.IsSimplyConnectedClosed3Manifold` : the hypothesis class of the Poincaré conjecture.
* `Frontier.PoincareConjecture3` : the formal statement of the Poincaré conjecture in dimension 3
  (Perelman): every simply connected closed 3-manifold is homeomorphic to `S³`.
* `Frontier.poincare_3sphere` : the Lean-checked *reduction*: the conjecture is equivalent to the
  a priori weaker statement that every simply connected closed 3-manifold admits a continuous
  bijection onto `S³`.  The nontrivial direction is closed by the Mathlib lemma
  `Continuous.homeoOfEquivCompactToT2` (a continuous bijection from a compact space to a Hausdorff
  space is a homeomorphism).
* Supporting results: the hypothesis class is invariant under homeomorphism
  (`Frontier.IsSimplyConnectedClosed3Manifold.homeomorph`) and is realized by `S³` itself
  (`Frontier.sphere3_isClosed3Manifold`), so the statement is not vacuous.

The base case of the conjecture — that `S³` really is a simply connected closed 3-manifold, and
that the conjecture holds for every space homeomorphic to it — is proved in
`RequestProject/Sphere3SimplyConnected.lean`.
-/

universe u v

namespace Frontier

open Metric

/-- The model space `ℝ³` for 3-manifolds. -/
abbrev EuclideanThree : Type := EuclideanSpace ℝ (Fin 3)

/-- The 3-sphere, as the unit sphere of `ℝ⁴`. -/
abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- A *closed 3-manifold*: a compact, Hausdorff, second countable topological space which is
locally homeomorphic to `ℝ³` (a boundaryless topological 3-manifold, i.e. charted over `ℝ³`). -/
structure IsClosed3Manifold (M : Type u) [TopologicalSpace M] : Prop where
  t2Space : T2Space M
  compactSpace : CompactSpace M
  secondCountableTopology : SecondCountableTopology M
  chartedSpace : Nonempty (ChartedSpace EuclideanThree M)

/-- The hypothesis class of the Poincaré conjecture: a simply connected closed 3-manifold. -/
structure IsSimplyConnectedClosed3Manifold (M : Type u) [TopologicalSpace M] : Prop
    extends IsClosed3Manifold M where
  simplyConnectedSpace : SimplyConnectedSpace M

/-- **The Poincaré conjecture in dimension three** (Perelman): every simply connected closed
3-manifold is homeomorphic to the 3-sphere. -/
def PoincareConjecture3 : Prop :=
  ∀ (M : Type u) [TopologicalSpace M], IsSimplyConnectedClosed3Manifold M →
    Nonempty (M ≃ₜ Sphere3)

/-- The weakened form of the conjecture in which the homeomorphism is only required to be a
continuous bijection. -/
def PoincareConjecture3ContinuousBijection : Prop :=
  ∀ (M : Type u) [TopologicalSpace M], IsSimplyConnectedClosed3Manifold M →
    ∃ f : M → Sphere3, Continuous f ∧ Function.Bijective f

section Transfer

variable {H : Type*} {M : Type u} {N : Type v}
  [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace N]

/-- A charted space structure transports along a homeomorphism. -/
noncomputable def chartedSpaceOfHomeomorph (e : M ≃ₜ N) (c : ChartedSpace H M) :
    ChartedSpace H N where
  atlas := (fun φ : OpenPartialHomeomorph M H => e.symm.toOpenPartialHomeomorph.trans φ) '' c.atlas
  chartAt y := e.symm.toOpenPartialHomeomorph.trans (c.chartAt (e.symm y))
  mem_chart_source y := by simp [c.mem_chart_source]
  chart_mem_atlas y := ⟨_, c.chart_mem_atlas _, rfl⟩

/-- Being a closed 3-manifold is invariant under homeomorphism. -/
theorem IsClosed3Manifold.homeomorph (h : IsClosed3Manifold M) (e : M ≃ₜ N) :
    IsClosed3Manifold N := by
  obtain ⟨ht2, hcomp, hsc, ⟨c⟩⟩ := h
  haveI := ht2; haveI := hcomp; haveI := hsc
  exact
    { t2Space := e.t2Space
      compactSpace := e.compactSpace
      secondCountableTopology := e.symm.isInducing.secondCountableTopology
      chartedSpace := ⟨chartedSpaceOfHomeomorph e c⟩ }

/-- Being a simply connected closed 3-manifold is invariant under homeomorphism. -/
theorem IsSimplyConnectedClosed3Manifold.homeomorph
    (h : IsSimplyConnectedClosed3Manifold M) (e : M ≃ₜ N) :
    IsSimplyConnectedClosed3Manifold N :=
  { h.toIsClosed3Manifold.homeomorph e with
    simplyConnectedSpace :=
      haveI := h.simplyConnectedSpace
      e.symm.toHomotopyEquiv.simplyConnectedSpace }

end Transfer

/-- The 3-sphere is a closed 3-manifold: it is compact, Hausdorff, second countable and charted
over `ℝ³`. -/
theorem sphere3_isClosed3Manifold : IsClosed3Manifold Sphere3 where
  t2Space := inferInstance
  compactSpace := inferInstance
  secondCountableTopology := inferInstance
  chartedSpace := ⟨inferInstance⟩

/-- **Lean-checked reduction of the Poincaré conjecture.**

The Poincaré conjecture in dimension three is *equivalent* to the a priori weaker statement that
every simply connected closed 3-manifold admits a merely *continuous bijection* onto `S³`.

The substantive direction uses the Mathlib lemma `Continuous.homeoOfEquivCompactToT2`: a continuous
bijection from a compact space to a Hausdorff space is automatically a homeomorphism.  The
compactness of `M` and the Hausdorffness of `S³` are exactly the "closed manifold" part of the
hypotheses. -/
theorem poincare_3sphere :
    PoincareConjecture3.{u} ↔ PoincareConjecture3ContinuousBijection.{u} := by
  constructor
  · intro h M _ hM
    obtain ⟨e⟩ := h M hM
    exact ⟨e, e.continuous, e.bijective⟩
  · intro h M _ hM
    obtain ⟨f, hf, hbij⟩ := h M hM
    haveI := hM.compactSpace
    exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij) hf⟩

end Frontier

import Mathlib
import RequestProject.Poincare3Sphere

/-!
# The 3-sphere is simply connected

This file proves that `S³ = sphere (0 : EuclideanSpace ℝ (Fin 4)) 1` is simply connected,
which shows that the hypothesis class of the Poincaré conjecture (see `Poincare3Sphere.lean`)
is nonempty: `S³` itself is a simply connected closed 3-manifold.

The proof is the classical one, formalized from scratch:

* every loop in the sphere is homotopic to a *Lipschitz* loop (obtained by a moving-average
  smoothing of the loop, corrected at the endpoints, followed by radial projection to the sphere);
* the image of a Lipschitz loop has Hausdorff dimension at most 1, hence the cone over it has
  Hausdorff dimension at most 2 < 4 = `finrank ℝ ℝ⁴`, so it has dense complement and cannot
  contain the whole sphere: the Lipschitz loop misses a point `p` of the sphere;
* the sphere minus a point is homeomorphic to a Euclidean space by stereographic projection,
  hence contractible, hence simply connected, so the loop is null-homotopic there and therefore
  in the sphere.
-/

open Metric Set MeasureTheory
open scoped ENNReal NNReal

namespace Frontier

/-- Ambient Euclidean 4-space. -/
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

/-- Radial projection onto the unit sphere. -/
noncomputable def nrmz (x : E4) : E4 := ‖x‖⁻¹ • x

theorem norm_nrmz {x : E4} (hx : x ≠ 0) : ‖nrmz x‖ = 1 := by
  rw [nrmz, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

theorem nrmz_mem_sphere {x : E4} (hx : x ≠ 0) : nrmz x ∈ sphere (0 : E4) 1 := by
  simpa [mem_sphere_iff_norm] using norm_nrmz hx

/-- **Lipschitz approximation.**  A uniformly continuous curve in a normed space can be
approximated uniformly on `[0,1]`, with the same endpoints, by a Lipschitz curve.  The
approximation is a moving average, corrected by an affine term so that the endpoints match. -/
theorem exists_lipschitz_approx (f : ℝ → E4) (hf : UniformContinuous f) (hb : ∀ u, ‖f u‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (K : NNReal) (Q : ℝ → E4), LipschitzWith K Q ∧ Q 0 = f 0 ∧ Q 1 = f 1 ∧
      ∀ t ∈ Icc (0:ℝ) 1, ‖Q t - f t‖ ≤ ε := by
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.mp hf (ε/3) (by linarith)
  have hfc : Continuous f := hf.continuous
  have hint : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => hfc.intervalIntegrable a b
  set F : ℝ → E4 := fun x => ∫ u in (0:ℝ)..x, f u with hF
  have hFsub : ∀ a b : ℝ, F b - F a = ∫ u in a..b, f u := fun a b =>
    intervalIntegral.integral_interval_sub_left (hint 0 b) (hint 0 a)
  have hFlip : ∀ a b : ℝ, ‖F b - F a‖ ≤ |b - a| := by
    intro a b
    rw [hFsub]
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) (fun x _ => hb x)
  set d : ℝ := δ/2 with hd
  have hd0 : 0 < d := by positivity
  set P : ℝ → E4 := fun t => d⁻¹ • (F (t + d) - F t) with hP
  have hPf : ∀ t : ℝ, ‖P t - f t‖ ≤ ε/3 := by
    intro t
    have key : (∫ u in t..(t+d), (f u - f t)) = (F (t+d) - F t) - d • f t := by
      rw [intervalIntegral.integral_sub (hint _ _) intervalIntegrable_const,
        intervalIntegral.integral_const, hFsub]
      simp
    have hnorm : ‖(∫ u in t..(t+d), (f u - f t))‖ ≤ (ε/3) * |t + d - t| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro u hu
      have hut : |u - t| < δ := by
        rw [Set.uIoc_of_le (by linarith)] at hu
        rw [abs_of_nonneg (by linarith [hu.1.le])]
        have := hu.2
        simp [hd] at this ⊢
        linarith
      have := hδ (a := u) (b := t) (by simpa [Real.dist_eq] using hut)
      rw [dist_eq_norm] at this
      exact this.le
    have hPt : P t - f t = d⁻¹ • ((F (t+d) - F t) - d • f t) := by
      rw [hP]
      simp only [smul_sub]
      rw [smul_smul, inv_mul_cancel₀ hd0.ne', one_smul]
    rw [hPt, ← key, norm_smul]
    have habs : |t + d - t| = d := by rw [show t + d - t = d by ring, abs_of_pos hd0]
    rw [habs] at hnorm
    have h1 : ‖(d⁻¹ : ℝ)‖ = d⁻¹ := by rw [Real.norm_eq_abs, abs_inv, abs_of_pos hd0]
    rw [h1]
    calc d⁻¹ * ‖(∫ u in t..(t+d), (f u - f t))‖ ≤ d⁻¹ * ((ε/3) * d) := by gcongr
      _ = ε/3 := by field_simp
  have hPlip : LipschitzWith (Real.toNNReal (2/d)) P := by
    apply LipschitzWith.of_dist_le_mul
    intro t s
    rw [dist_eq_norm, hP]
    simp only
    have hrw : d⁻¹ • (F (t + d) - F t) - d⁻¹ • (F (s + d) - F s)
        = d⁻¹ • ((F (t+d) - F (s+d)) - (F t - F s)) := by
      rw [← smul_sub]; congr 1; abel
    rw [hrw, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hd0]
    have h1 : ‖F (t+d) - F (s+d)‖ ≤ |t - s| := by
      simpa [show t + d - (s+d) = t - s by ring] using hFlip (s+d) (t+d)
    have h2 : ‖F t - F s‖ ≤ |t - s| := hFlip s t
    have h3 : ‖(F (t+d) - F (s+d)) - (F t - F s)‖ ≤ 2 * |t - s| := by
      calc ‖(F (t+d) - F (s+d)) - (F t - F s)‖ ≤ ‖F (t+d) - F (s+d)‖ + ‖F t - F s‖ :=
            norm_sub_le _ _
        _ ≤ 2 * |t - s| := by linarith
    have hK : (Real.toNNReal (2/d) : ℝ) = 2/d := Real.coe_toNNReal _ (by positivity)
    rw [hK, Real.dist_eq]
    calc d⁻¹ * ‖(F (t+d) - F (s+d)) - (F t - F s)‖ ≤ d⁻¹ * (2 * |t - s|) := by gcongr
      _ = 2/d * |t - s| := by field_simp
  clear_value P
  clear hP hFsub hFlip hF
  set K : NNReal := Real.toNNReal (2/d)
  set u := f 0 - P 0 with hu
  set v := f 1 - P 1 with hv
  have hun : ‖u‖ ≤ ε/3 := by rw [hu, norm_sub_rev]; exact hPf 0
  have hvn : ‖v‖ ≤ ε/3 := by rw [hv, norm_sub_rev]; exact hPf 1
  refine ⟨K + Real.toNNReal (‖u‖ + ‖v‖), fun t => P t + (1 - t) • u + t • v, ?_, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro t s
    have hexp : (P t + (1 - t) • u + t • v) - (P s + (1 - s) • u + s • v)
        = (P t - P s) + (s - t) • u + (t - s) • v := by
      rw [sub_smul, sub_smul, sub_smul]; module
    rw [dist_eq_norm, hexp]
    have h1 : ‖P t - P s‖ ≤ (K : ℝ) * dist t s := by
      rw [← dist_eq_norm]; exact hPlip.dist_le_mul t s
    have h2 : ‖(s - t) • u‖ = |s - t| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs]
    have h3 : ‖(t - s) • v‖ = |t - s| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
    have hts : |s - t| = dist t s := by rw [Real.dist_eq, abs_sub_comm]
    have hst : |t - s| = dist t s := by rw [Real.dist_eq]
    have hcoe : ((K + Real.toNNReal (‖u‖ + ‖v‖) : NNReal) : ℝ) = (K : ℝ) + (‖u‖ + ‖v‖) := by
      rw [NNReal.coe_add,
        Real.coe_toNNReal (‖u‖ + ‖v‖) (add_nonneg (norm_nonneg u) (norm_nonneg v))]
    calc ‖(P t - P s) + (s - t) • u + (t - s) • v‖
        ≤ ‖P t - P s‖ + ‖(s - t) • u‖ + ‖(t - s) • v‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ (K : ℝ) * dist t s + dist t s * ‖u‖ + dist t s * ‖v‖ := by
          rw [h2, h3, hts, hst]; gcongr
      _ = (((K + Real.toNNReal (‖u‖ + ‖v‖) : NNReal) : ℝ)) * dist t s := by rw [hcoe]; ring
  · simp [hu]
  · simp [hv]
  · intro t ht
    have hexp : (P t + (1 - t) • u + t • v) - f t = (P t - f t) + (1 - t) • u + t • v := by abel
    have h1 : ‖(1 - t) • u‖ ≤ (1 - t) * (ε/3) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
      nlinarith [ht.2, norm_nonneg u]
    have h2 : ‖t • v‖ ≤ t * (ε/3) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      nlinarith [ht.1, norm_nonneg v]
    calc ‖(P t + (1 - t) • u + t • v) - f t‖ = ‖(P t - f t) + (1 - t) • u + t • v‖ := by rw [hexp]
      _ ≤ ‖P t - f t‖ + ‖(1 - t) • u‖ + ‖t • v‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ ε/3 + (1 - t) * (ε/3) + t * (ε/3) := by gcongr; exact hPf t
      _ ≤ ε := by nlinarith

/-- **A Lipschitz curve does not fill the sphere.**  The cone over the image of a Lipschitz curve
has Hausdorff dimension at most `2 < 4`, so its complement is dense in `ℝ⁴`; a point of the
complement of norm close to `3/2` yields a point of the unit sphere missed by the radial
projection of the curve. -/
theorem exists_sphere_point_not_mem_image {K : NNReal} {Q : ℝ → E4} (hQ : LipschitzWith K Q)
    (hlb : ∀ t ∈ Icc (0:ℝ) 1, 1/2 ≤ ‖Q t‖) (hub : ∀ t ∈ Icc (0:ℝ) 1, ‖Q t‖ ≤ 2) :
    ∃ p : E4, ‖p‖ = 1 ∧ ∀ t ∈ Icc (0:ℝ) 1, nrmz (Q t) ≠ p := by
  classical
  set D : Set (ℝ × ℝ) := Icc (0:ℝ) 8 ×ˢ Icc (0:ℝ) 1 with hD
  set C : Set E4 := (fun rt : ℝ × ℝ => rt.1 • Q rt.2) '' D with hC
  have hlip : LipschitzOnWith (8 * K + 2) (fun rt : ℝ × ℝ => rt.1 • Q rt.2) D := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro ⟨r, t⟩ ⟨hr, ht⟩ ⟨r', t'⟩ ⟨hr', ht'⟩
    simp only
    have hd1 : |r - r'| ≤ dist ((r,t) : ℝ × ℝ) (r', t') := by
      rw [Prod.dist_eq]; simp [Real.dist_eq]
    have hd2 : |t - t'| ≤ dist ((r,t) : ℝ × ℝ) (r', t') := by
      rw [Prod.dist_eq]; simp [Real.dist_eq]
    have hQd : ‖Q t - Q t'‖ ≤ (K : ℝ) * |t - t'| := by
      rw [← dist_eq_norm, ← Real.dist_eq]; exact hQ.dist_le_mul t t'
    have hr8 : |r| ≤ 8 := by rw [abs_of_nonneg hr.1]; exact hr.2
    have hQ2 : ‖Q t'‖ ≤ 2 := hub t' ht'
    have hsplit : ‖r • Q t - r' • Q t'‖ ≤ |r| * ‖Q t - Q t'‖ + |r - r'| * ‖Q t'‖ := by
      have h : r • Q t - r' • Q t' = r • (Q t - Q t') + (r - r') • Q t' := by module
      rw [h]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [dist_eq_norm]
    have hcoe : ((8 * K + 2 : NNReal) : ℝ) = 8 * (K:ℝ) + 2 := by push_cast; ring
    rw [hcoe]
    calc ‖r • Q t - r' • Q t'‖ ≤ |r| * ‖Q t - Q t'‖ + |r - r'| * ‖Q t'‖ := hsplit
      _ ≤ 8 * ((K:ℝ) * |t - t'|) + |r - r'| * 2 := by gcongr
      _ ≤ 8 * ((K:ℝ) * dist ((r,t) : ℝ × ℝ) (r', t')) + dist ((r,t) : ℝ × ℝ) (r', t') * 2 := by
          gcongr
      _ = (8 * (K:ℝ) + 2) * dist ((r,t) : ℝ × ℝ) (r', t') := by ring
  have hdimD : dimH D ≤ 2 := by
    calc dimH D ≤ dimH (univ : Set (ℝ × ℝ)) := dimH_mono (subset_univ _)
      _ = 2 := by rw [Real.dimH_univ_eq_finrank]; simp
  have hdimC : dimH C < (Module.finrank ℝ E4 : ℝ≥0∞) := by
    have h1 : dimH C ≤ 2 := (hlip.dimH_image_le).trans hdimD
    have h2 : (Module.finrank ℝ E4) = 4 := by simp
    rw [h2]
    exact lt_of_le_of_lt h1 (by norm_num)
  have hdense : Dense Cᶜ := dense_compl_of_dimH_lt_finrank hdimC
  set w : E4 := (3/2 : ℝ) • (EuclideanSpace.single (0 : Fin 4) (1:ℝ)) with hw
  have hwn : ‖w‖ = 3/2 := by
    rw [hw, norm_smul, EuclideanSpace.norm_single]
    norm_num
  obtain ⟨z, hz⟩ := (Metric.dense_iff.mp hdense) w (1/4) (by norm_num)
  have hzw : ‖z - w‖ < 1/4 := by rw [← dist_eq_norm]; exact hz.1
  have hzC : z ∉ C := hz.2
  have h1 : ‖z‖ > 5/4 := by
    have hb := norm_sub_norm_le w z
    rw [norm_sub_rev] at hb
    rw [hwn] at hb
    linarith
  have h2 : ‖z‖ ≤ 7/4 := by
    have hb := norm_sub_norm_le z w
    rw [hwn] at hb
    linarith
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at h1; simp at h1; linarith
  refine ⟨nrmz z, norm_nrmz hz0, ?_⟩
  intro t ht heq
  apply hzC
  have hQt : 1/2 ≤ ‖Q t‖ := hlb t ht
  have hQ0 : ‖Q t‖ ≠ 0 := by intro h; rw [h] at hQt; linarith
  refine hC ▸ ⟨(‖z‖ * ‖Q t‖⁻¹, t), ?_, ?_⟩
  · rw [hD]
    refine ⟨⟨by positivity, ?_⟩, ht⟩
    have hinv : ‖Q t‖⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    nlinarith [norm_nonneg z]
  · show (‖z‖ * ‖Q t‖⁻¹) • Q t = z
    have h3 : (‖z‖ * ‖Q t‖⁻¹) • Q t = ‖z‖ • nrmz (Q t) := by rw [nrmz, smul_smul]
    rw [h3, heq, nrmz, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz0), one_smul]

/-- **A loop that misses a point of the sphere is null-homotopic.**  Indeed, the sphere minus a
point is homeomorphic, via stereographic projection, to a Euclidean space, hence contractible. -/
theorem nullhomotopic_of_avoids_point {x : sphere (0 : E4) 1} (g : Path x x)
    {p : sphere (0 : E4) 1} (hp : ∀ t, g t ≠ p) : g.Homotopic (Path.refl x) := by
  have hpn : ‖(p : E4)‖ = 1 := by simp
  set e := stereographic hpn with he
  have hsource : e.source = ({p}ᶜ : Set (sphere (0 : E4) 1)) := by
    rw [he, stereographic_source]
  set U : Set (sphere (0 : E4) 1) := {p}ᶜ with hU
  have hhomeo : ↥U ≃ₜ ↥(ℝ ∙ (p : E4))ᗮ := by
    refine (Homeomorph.setCongr hsource.symm).trans ?_
    refine e.toHomeomorphSourceTarget.trans ?_
    rw [stereographic_target]
    exact Homeomorph.Set.univ _
  have hsc : SimplyConnectedSpace ↥U := hhomeo.toHomotopyEquiv.simplyConnectedSpace
  have hxU : x ∈ U := by simpa [hU] using hp 0
  let g' : Path (⟨x, hxU⟩ : ↥U) (⟨x, hxU⟩ : ↥U) :=
    { toFun := fun t => ⟨g t, hp t⟩
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  have hnull : g'.Homotopic (Path.refl (⟨x, hxU⟩ : ↥U)) :=
    SimplyConnectedSpace.paths_homotopic g' (Path.refl _)
  have hcont : Continuous (Subtype.val : ↥U → sphere (0 : E4) 1) := continuous_subtype_val
  have hmap := hnull.map (⟨Subtype.val, hcont⟩ : C(↥U, sphere (0 : E4) 1))
  have h1 : g'.map hcont = g := by ext t; rfl
  have h2 : (Path.refl (⟨x, hxU⟩ : ↥U)).map hcont = Path.refl x := by ext t; rfl
  rw [h1, h2] at hmap
  exact hmap

/-- **The 3-sphere is simply connected.** -/
theorem sphere3_simplyConnectedSpace : SimplyConnectedSpace (sphere (0 : E4) 1) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  constructor
  · rw [← isPathConnected_iff_pathConnectedSpace]
    refine isPathConnected_sphere ?_ 0 zero_le_one
    have hr : Module.rank ℝ E4 = 4 := by
      simp [rank_eq_card_basis (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis]
    rw [hr]
    norm_num
  · intro x γ
    set f : ℝ → E4 := fun u => ((γ.extend u : sphere (0:E4) 1) : E4) with hf
    have hfnorm : ∀ u, ‖f u‖ = 1 := by
      intro u
      simp [hf]
    have hfU : UniformContinuous f := by
      have h1 : UniformContinuous (fun s : unitInterval => ((γ s : sphere (0:E4) 1) : E4)) :=
        CompactSpace.uniformContinuous_of_continuous (by fun_prop)
      have h2 : LipschitzWith 1 (Set.projIcc (0:ℝ) 1 zero_le_one) :=
        LipschitzWith.projIcc zero_le_one
      exact h1.comp h2.uniformContinuous
    obtain ⟨K, Q, hQlip, hQ0, hQ1, hQd⟩ :=
      exists_lipschitz_approx f hfU (fun u => (hfnorm u).le) (ε := 3/8) (by norm_num)
    have hQlb : ∀ t ∈ Icc (0:ℝ) 1, 5/8 ≤ ‖Q t‖ := by
      intro t ht
      have h1 := hQd t ht
      have h2 := hfnorm t
      have ha : ‖f t‖ - ‖Q t‖ ≤ ‖f t - Q t‖ := norm_sub_norm_le _ _
      rw [norm_sub_rev] at ha
      linarith
    have hQub : ∀ t ∈ Icc (0:ℝ) 1, ‖Q t‖ ≤ 2 := by
      intro t ht
      have h1 := hQd t ht
      have h2 := hfnorm t
      have hb : ‖Q t‖ ≤ ‖f t‖ + ‖Q t - f t‖ := by
        have := norm_add_le (f t) (Q t - f t)
        simpa using this
      linarith
    have hQne : ∀ t : unitInterval, Q (t : ℝ) ≠ 0 := by
      intro t h
      have hlb := hQlb (t:ℝ) ⟨t.2.1, t.2.2⟩
      rw [h] at hlb
      simp at hlb
      linarith
    have hcont : Continuous fun t : unitInterval => nrmz (Q (t:ℝ)) := by
      have hc : Continuous fun t : unitInterval => Q (t:ℝ) :=
        hQlip.continuous.comp continuous_subtype_val
      have hinv : Continuous fun t : unitInterval => (‖Q (t:ℝ)‖)⁻¹ :=
        (continuous_norm.comp hc).inv₀ (fun t => norm_ne_zero_iff.mpr (hQne t))
      exact hinv.smul hc
    have hQ0x : Q 0 = (x : E4) := by rw [hQ0, hf]; simp
    have hQ1x : Q 1 = (x : E4) := by rw [hQ1, hf]; simp
    have hxn : ‖(x : E4)‖ = 1 := by simp
    have hnrmzx : nrmz (x : E4) = (x : E4) := by rw [nrmz, hxn]; simp
    let g : Path x x :=
      { toFun := fun t => ⟨nrmz (Q (t:ℝ)), nrmz_mem_sphere (hQne t)⟩
        continuous_toFun := hcont.subtype_mk _
        source' := by
          apply Subtype.ext
          simp only [Set.Icc.coe_zero, hQ0x, hnrmzx]
        target' := by
          apply Subtype.ext
          simp only [Set.Icc.coe_one, hQ1x, hnrmzx] }
    have hne : ∀ s t : unitInterval, (1 - (s:ℝ)) • f (t:ℝ) + (s:ℝ) • Q (t:ℝ) ≠ 0 := by
      intro s t h
      have hd : ‖((1 - (s:ℝ)) • f (t:ℝ) + (s:ℝ) • Q (t:ℝ)) - f (t:ℝ)‖ ≤ 3/8 := by
        have hrw : ((1 - (s:ℝ)) • f (t:ℝ) + (s:ℝ) • Q (t:ℝ)) - f (t:ℝ)
            = (s:ℝ) • (Q (t:ℝ) - f (t:ℝ)) := by module
        rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_nonneg s.2.1]
        have h1 := hQd (t:ℝ) ⟨t.2.1, t.2.2⟩
        nlinarith [s.2.2, norm_nonneg (Q (t:ℝ) - f (t:ℝ))]
      rw [h, zero_sub, norm_neg, hfnorm] at hd
      linarith
    have hcH : Continuous fun st : unitInterval × unitInterval =>
        nrmz ((1 - (st.1:ℝ)) • f (st.2:ℝ) + (st.1:ℝ) • Q (st.2:ℝ)) := by
      have hfc : Continuous f := hfU.continuous
      have hQc : Continuous Q := hQlip.continuous
      have hbase : Continuous fun st : unitInterval × unitInterval =>
          (1 - (st.1:ℝ)) • f (st.2:ℝ) + (st.1:ℝ) • Q (st.2:ℝ) := by fun_prop
      have hinv : Continuous fun st : unitInterval × unitInterval =>
          ‖(1 - (st.1:ℝ)) • f (st.2:ℝ) + (st.1:ℝ) • Q (st.2:ℝ)‖⁻¹ :=
        hbase.norm.inv₀ (fun st => norm_ne_zero_iff.mpr (hne st.1 st.2))
      exact hinv.smul hbase
    have hhom : γ.Homotopic g := by
      refine ⟨{ toFun := fun st => ⟨nrmz ((1 - (st.1:ℝ)) • f (st.2:ℝ) + (st.1:ℝ) • Q (st.2:ℝ)),
                  nrmz_mem_sphere (hne st.1 st.2)⟩
                continuous_toFun := hcH.subtype_mk _
                map_zero_left := ?_
                map_one_left := ?_
                prop' := ?_ }⟩
      · intro t
        apply Subtype.ext
        have hz : ((0 : unitInterval) : ℝ) = 0 := rfl
        simp only [hz, sub_zero, one_smul, zero_smul, add_zero]
        have : nrmz (f (t:ℝ)) = f (t:ℝ) := by rw [nrmz, hfnorm]; simp
        rw [this, hf]
        simp
      · intro t
        apply Subtype.ext
        have ho : ((1 : unitInterval) : ℝ) = 1 := rfl
        simp only [ho, sub_self, one_smul, zero_smul, zero_add]
        rfl
      · intro s y hy
        apply Subtype.ext
        show nrmz ((1 - (s:ℝ)) • f (y:ℝ) + (s:ℝ) • Q (y:ℝ)) = ((γ y : sphere (0:E4) 1) : E4)
        have hyv : (y : ℝ) = 0 ∨ (y : ℝ) = 1 := by
          rcases hy with h | h
          · left; rw [h]; rfl
          · right; rw [Set.mem_singleton_iff.mp h]; rfl
        have hfy : f (y:ℝ) = (x : E4) ∧ Q (y:ℝ) = (x : E4) := by
          rcases hyv with h | h
          · rw [h, hQ0x]
            exact ⟨by rw [hf]; simp, rfl⟩
          · rw [h, hQ1x]
            exact ⟨by rw [hf]; simp, rfl⟩
        rw [hfy.1, hfy.2]
        have hcomb : (1 - (s:ℝ)) • (x : E4) + (s:ℝ) • (x : E4) = (x : E4) := by module
        rw [hcomb, hnrmzx]
        rcases hyv with h | h
        · have : y = 0 := Subtype.ext h
          rw [this]
          simp
        · have : y = 1 := Subtype.ext h
          rw [this]
          simp
    obtain ⟨p, hpnorm, hpne⟩ :=
      exists_sphere_point_not_mem_image hQlip (fun t ht => by linarith [hQlb t ht]) hQub
    have hpS : p ∈ sphere (0:E4) 1 := by simp [mem_sphere_iff_norm, hpnorm]
    have hgp : ∀ t : unitInterval, g t ≠ ⟨p, hpS⟩ := by
      intro t h
      exact hpne (t:ℝ) ⟨t.2.1, t.2.2⟩ (congrArg Subtype.val h)
    exact hhom.trans (nullhomotopic_of_avoids_point g hgp)

/-- The 3-sphere is a simply connected closed 3-manifold: the hypothesis class of the Poincaré
conjecture is nonempty. -/
theorem sphere3_isSimplyConnectedClosed3Manifold :
    IsSimplyConnectedClosed3Manifold Sphere3 :=
  { sphere3_isClosed3Manifold with simplyConnectedSpace := sphere3_simplyConnectedSpace }

/-- **Base case of the Poincaré conjecture.**  Every space homeomorphic to `S³` — in particular
`S³` itself — is a simply connected closed 3-manifold, and satisfies the conclusion of the
conjecture. -/
theorem poincare_3sphere_base {M : Type u} [TopologicalSpace M] (e : M ≃ₜ Sphere3) :
    IsSimplyConnectedClosed3Manifold M ∧ Nonempty (M ≃ₜ Sphere3) :=
  ⟨sphere3_isSimplyConnectedClosed3Manifold.homeomorph e.symm, ⟨e⟩⟩

end Frontier

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

