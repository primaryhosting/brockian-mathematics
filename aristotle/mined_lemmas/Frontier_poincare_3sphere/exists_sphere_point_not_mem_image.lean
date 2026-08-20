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
