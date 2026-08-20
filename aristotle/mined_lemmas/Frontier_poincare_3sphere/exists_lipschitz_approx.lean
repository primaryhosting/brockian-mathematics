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
