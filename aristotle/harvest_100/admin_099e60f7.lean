import Mathlib

/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Metric Filter Set Topology
open scoped ENNReal

namespace Frontier

/-! ## Setup

Uhlenbeck's compactness theorem for Yang–Mills connections asserts that a sequence of
connections with uniformly bounded Yang–Mills energy converges (after gauge transformations
and passing to a subsequence) away from a *finite* set of points, the *bubbling points*,
at which a definite quantum of energy concentrates.

The quantitative combinatorial heart of that statement — the part that is independent of
gauge theory and is what actually produces the finiteness of the bubbling set — is the
following: if `ν i` is the sequence of energy measures, uniformly bounded by `E`, then the
set of points at which at least `ε₀` of energy concentrates in every ball is finite, of
cardinality at most `E / ε₀`.  (The gauge-theoretic input, `ε`-regularity, is what
guarantees that away from this set the connections converge; it is not formalized here.)

We formalize this statement and prove it. -/

/-- The *energy measure* attached to a curvature field `F` on a measure space `(X, μ)`:
the measure with density `‖F x‖ ^ 2` with respect to `μ`.  For a Yang–Mills connection `A`
on `ℝ⁴` with curvature `F_A`, this is the measure `|F_A|² dvol` whose total mass is the
Yang–Mills energy. -/
noncomputable def energyMeasure {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {V : Type*} [NormedAddCommGroup V] (F : X → V) : Measure X :=
  μ.withDensity (fun x => (‖F x‖₊ : ℝ≥0∞) ^ 2)

/-- The *bubbling set* of a sequence of energy measures `ν` at concentration threshold `ε₀`:
the set of points `x` such that every ball around `x` carries, in the limit, at least `ε₀`
of energy. -/
def bubbleSet {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (ν : ℕ → Measure X) (ε₀ : ℝ≥0∞) : Set X :=
  {x | ∀ r : ℝ, 0 < r → ε₀ ≤ liminf (fun i => ν i (ball x r)) atTop}

/-! ## Auxiliary lemmas -/

/-- A finite set of points in a metric space can be surrounded by pairwise disjoint balls
of a common positive radius. -/
theorem exists_pos_pairwiseDisjoint_ball {X : Type*} [MetricSpace X] (T : Finset X) :
    ∃ r : ℝ, 0 < r ∧ (↑T : Set X).PairwiseDisjoint (fun x => ball x r) := by
  obtain ⟨C, hC0, hC⟩ := (T.finite_toSet).relatively_discrete
  set C' : ℝ≥0∞ := min C 1 with hC'
  have hC'0 : 0 < C' := lt_min hC0 (by norm_num)
  have hC'top : C' ≠ ⊤ := by
    refine ne_top_of_le_ne_top (by norm_num) (min_le_right _ _)
  have hpos : 0 < C'.toReal := ENNReal.toReal_pos hC'0.ne' hC'top
  refine ⟨C'.toReal / 2, by linarith, ?_⟩
  intro x hx y hy hxy
  refine Metric.ball_disjoint_ball ?_
  have hle : C' ≤ edist x y := le_trans (min_le_left _ _) (hC x hx y hy hxy)
  have : C'.toReal ≤ (edist x y).toReal :=
    ENNReal.toReal_mono (edist_ne_top x y) hle
  rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at this
  linarith

/-- **Energy quantization bound.**  Any finite set of bubbling points has cardinality at
most `E / ε₀`, stated multiplicatively. -/
theorem card_mul_le_of_subset_bubbleSet {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (ν : ℕ → Measure X) (E ε₀ : ℝ≥0∞)
    (hε₀ : ε₀ ≠ 0) (hε₀' : ε₀ ≠ ⊤) (hbound : ∀ i, ν i Set.univ ≤ E)
    (T : Finset X) (hT : ↑T ⊆ bubbleSet ν ε₀) :
    (T.card : ℝ≥0∞) * ε₀ ≤ E := by
  obtain ⟨r, hr, hdisj⟩ := exists_pos_pairwiseDisjoint_ball T
  -- It suffices to bound `T.card * c` for every `c < ε₀`.
  have key : ∀ c : ℝ≥0∞, c < ε₀ → (T.card : ℝ≥0∞) * c ≤ E := by
    intro c hc
    have hev : ∀ᶠ i in atTop, ∀ x ∈ T, c < ν i (ball x r) := by
      rw [eventually_all_finset]
      intro x hx
      exact eventually_lt_of_lt_liminf (lt_of_lt_of_le hc (hT hx r hr))
    obtain ⟨i, hi⟩ := hev.exists
    calc (T.card : ℝ≥0∞) * c = ∑ _x ∈ T, c := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ T, ν i (ball x r) := Finset.sum_le_sum fun x hx => (hi x hx).le
      _ = ν i (⋃ x ∈ T, ball x r) :=
          (measure_biUnion_finset hdisj fun x _ => measurableSet_ball).symm
      _ ≤ ν i Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ E := hbound i
  -- Now let `c ↑ ε₀`.
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
  have hlt : a * ε₀ < ε₀ := by
    calc a * ε₀ = ε₀ * a := mul_comm _ _
      _ < ε₀ * 1 := ENNReal.mul_lt_mul_right hε₀ hε₀' ha
      _ = ε₀ := mul_one _
  calc a * ((T.card : ℝ≥0∞) * ε₀) = (T.card : ℝ≥0∞) * (a * ε₀) := by ring
    _ ≤ E := key _ hlt

/-! ## Main theorem -/

/-- **Uhlenbeck bubbling: finiteness and energy quantization of the bubbling set.**

If `ν : ℕ → Measure X` is a sequence of energy measures on a metric space with total mass
uniformly bounded by `E < ∞`, and `ε₀ ∈ (0, ∞)` is a concentration threshold, then the set
of bubbling points — the points at which at least `ε₀` of energy concentrates in every
ball, in the `liminf` sense — is finite, and its cardinality `N` satisfies `N · ε₀ ≤ E`;
that is, at most `E / ε₀` bubbles can form. -/
theorem uhlenbeck_bubbling {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (ν : ℕ → Measure X) (E ε₀ : ℝ≥0∞)
    (hE : E ≠ ⊤) (hε₀ : ε₀ ≠ 0) (hε₀' : ε₀ ≠ ⊤) (hbound : ∀ i, ν i Set.univ ≤ E) :
    (bubbleSet ν ε₀).Finite ∧ ((bubbleSet ν ε₀).ncard : ℝ≥0∞) * ε₀ ≤ E := by
  have key := card_mul_le_of_subset_bubbleSet ν E ε₀ hε₀ hε₀' hbound
  have hfin : (bubbleSet ν ε₀).Finite := by
    by_contra hinf
    rw [Set.not_finite] at hinf
    obtain ⟨n, hn⟩ : ∃ n : ℕ, E < n * ε₀ := by
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (r := E / ε₀)
        (by simp [ENNReal.div_eq_top, hε₀, hE])
      exact ⟨n, by rwa [ENNReal.div_lt_iff (Or.inl hε₀) (Or.inl hε₀')] at hn⟩
    obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq n
    exact absurd (key T hTsub) (by rw [hTcard]; exact not_le.2 hn)
  refine ⟨hfin, ?_⟩
  have := key hfin.toFinset (by rw [hfin.coe_toFinset])
  rwa [← Set.ncard_eq_toFinset_card _ hfin] at this

/-- **Uhlenbeck bubbling for Yang–Mills energy measures on Euclidean space.**

For a sequence of curvature fields `F i : ℝⁿ → V` with Yang–Mills energies
`∫ ‖F i‖² ≤ E < ∞`, the set of points where at least `ε₀` of energy concentrates is
finite, with at most `E / ε₀` points. -/
theorem uhlenbeck_bubbling_yangMills {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    (F : ℕ → EuclideanSpace ℝ (Fin n) → V) (E ε₀ : ℝ≥0∞)
    (hE : E ≠ ⊤) (hε₀ : ε₀ ≠ 0) (hε₀' : ε₀ ≠ ⊤)
    (hbound : ∀ i, ∫⁻ x, (‖F i x‖₊ : ℝ≥0∞) ^ 2 ≤ E) :
    (bubbleSet (fun i => energyMeasure volume (F i)) ε₀).Finite ∧
      ((bubbleSet (fun i => energyMeasure volume (F i)) ε₀).ncard : ℝ≥0∞) * ε₀ ≤ E := by
  refine uhlenbeck_bubbling _ E ε₀ hE hε₀ hε₀' fun i => ?_
  rw [energyMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hbound i

/-! ## Non-vacuity: a bubbling point really can occur

For the constant sequence of energy measures `ε₀ · δ_{x₀}` (a single bubble of energy `ε₀`
sitting at `x₀`), the bubbling set is exactly `{x₀}`, so the statement above is not vacuous:
it really does bound a nonempty bubbling set. -/
theorem bubbleSet_smul_dirac {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (x₀ : X) (ε₀ : ℝ≥0∞) (hε₀ : ε₀ ≠ 0) :
    bubbleSet (fun _ : ℕ => ε₀ • Measure.dirac x₀) ε₀ = {x₀} := by
  ext x
  simp only [bubbleSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    by_contra hne
    have hd : 0 < dist x x₀ := dist_pos.2 hne
    have := hx (dist x x₀ / 2) (by linarith)
    have hmem : x₀ ∉ ball x (dist x x₀ / 2) := by
      simp only [Metric.mem_ball, not_lt]
      rw [dist_comm x x₀] at hd ⊢
      linarith
    rw [show ((ε₀ • Measure.dirac x₀) (ball x (dist x x₀ / 2))) = 0 by
      simp [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_ball,
        Set.indicator_of_notMem hmem]] at this
    simp only [liminf_const] at this
    exact hε₀ (le_antisymm this (zero_le _))
  · rintro rfl r hr
    have hb : ((ε₀ • Measure.dirac x) (ball x r)) = ε₀ := by
      simp [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_ball,
        Set.indicator_of_mem (Metric.mem_ball_self hr)]
    simp [hb]

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

