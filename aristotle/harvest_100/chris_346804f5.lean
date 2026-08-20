/-
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
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

namespace Frontier

open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

/-- The *bubbling set* (concentration set) of a sequence of energy measures `mu n` at
concentration threshold `eps`: those points where, at every scale `r > 0`, at least `eps`
of the energy is asymptotically present. -/
def BubbleSet {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (mu : ℕ → Measure X) (eps : ℝ≥0∞) : Set X :=
  {x : X | ∀ r : ℝ, 0 < r → eps ≤ Filter.liminf (fun n : ℕ => mu n (Metric.ball x r)) atTop}

/-- Around the points of a finite set one can center pairwise disjoint balls. -/
private lemma exists_pos_pairwise_disjoint_ball {X : Type*} [MetricSpace X] (t : Finset X) :
    ∃ r : ℝ, 0 < r ∧
      (t : Set X).Pairwise (fun x y => Disjoint (Metric.ball x r) (Metric.ball y r)) := by
  rcases Set.subsingleton_or_nontrivial (t : Set X) with h | h
  · exact ⟨1, one_pos, h.pairwise _⟩
  · refine ⟨(t : Set X).infsep / 2, by
      have := (t.finite_toSet.infsep_pos_iff_nontrivial).2 h
      linarith, ?_⟩
    intro x hx y hy hxy
    refine Metric.ball_disjoint_ball ?_
    have := Set.infsep_le_dist_of_mem hx hy hxy
    linarith

/-- Key quantitative step: any finite family of bubbling points carries `eps` of energy each,
inside pairwise disjoint balls, hence its cardinality times `eps` is bounded by the total
energy bound `E`. -/
private lemma finset_card_mul_le_of_subset_bubbleSet {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (mu : ℕ → Measure X) (E eps : ℝ≥0∞)
    (hbound : ∀ n, mu n Set.univ ≤ E) (t : Finset X) (ht : (t : Set X) ⊆ BubbleSet mu eps) :
    (t.card : ℝ≥0∞) * eps ≤ E := by
  obtain ⟨r, hr, hdisj⟩ := exists_pos_pairwise_disjoint_ball t
  -- For every `b < eps`, all balls eventually have measure `> b` simultaneously.
  have key : ∀ b : ℝ≥0∞, b < eps → (t.card : ℝ≥0∞) * b ≤ E := by
    intro b hb
    have hev : ∀ᶠ n : ℕ in atTop, ∀ x ∈ t, b < mu n (Metric.ball x r) := by
      rw [Filter.eventually_all_finset]
      intro x hx
      exact Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le hb (ht hx r hr))
    obtain ⟨n, hn⟩ := hev.exists
    calc (t.card : ℝ≥0∞) * b = ∑ _x ∈ t, b := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ t, mu n (Metric.ball x r) :=
            Finset.sum_le_sum (fun x hx => (hn x hx).le)
      _ = mu n (⋃ x ∈ t, Metric.ball x r) := by
            rw [measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)]
      _ ≤ mu n Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ E := hbound n
  rcases Nat.eq_zero_or_pos t.card with h0 | h0
  · simp [h0]
  -- Pass to the supremum over `b < eps` using density of the order on `ℝ≥0∞`.
  have hcard0 : (t.card : ℝ≥0∞) ≠ 0 := by
    simpa using h0.ne'
  have hcardtop : (t.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hle : eps ≤ E / (t.card : ℝ≥0∞) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨c, hc1, hc2⟩ := exists_between hcon
    have hkey := key c hc2
    have : c ≤ E / (t.card : ℝ≥0∞) :=
      (ENNReal.le_div_iff_mul_le (Or.inl hcard0) (Or.inl hcardtop)).2
        (by rwa [mul_comm] at hkey)
    exact absurd this (not_le.2 hc1)
  calc (t.card : ℝ≥0∞) * eps ≤ (t.card : ℝ≥0∞) * (E / (t.card : ℝ≥0∞)) := by
        gcongr
    _ ≤ E := ENNReal.mul_div_le

/-- Sanity check (non-vacuity): a sequence of unit point masses at `x` does concentrate at `x`,
i.e. `x` really is a bubbling point at threshold `1`. -/
theorem mem_bubbleSet_dirac {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [MeasurableSingletonClass X] (x : X) :
    x ∈ BubbleSet (fun _ : ℕ => Measure.dirac x) 1 := by
  intro r hr
  have : (fun _ : ℕ => (Measure.dirac x) (Metric.ball x r)) = fun _ : ℕ => (1 : ℝ≥0∞) := by
    funext n
    rw [MeasureTheory.Measure.dirac_apply_of_mem (Metric.mem_ball_self hr)]
  rw [this]
  simp

/-- **Uhlenbeck bubbling: finiteness of the concentration set.**

Let `mu n` be the sequence of energy measures of a sequence of Yang–Mills connections
(`mu n = |F_{A_n}|² dvol`) on a metric measure space `X`, subject to a uniform energy bound
`mu n (univ) ≤ E < ∞`.  Fix a concentration threshold `eps > 0` (the `ε` of `ε`-regularity).
Then the bubbling set — the set of points at which at least `eps` of the energy concentrates
at every scale — is *finite*, and its cardinality obeys the quantization bound
`#(bubbling set) * eps ≤ E`.

This is the combinatorial/measure-theoretic core of Uhlenbeck's compactness theorem: away from
these finitely many points, the `ε`-regularity theorem applies and gives local convergence,
while each bubble point absorbs at least `eps` of energy. -/
theorem uhlenbeck_bubbling {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (mu : ℕ → Measure X) (E eps : ℝ≥0∞) (hE : E ≠ ⊤) (heps : eps ≠ 0)
    (hbound : ∀ n, mu n Set.univ ≤ E) :
    (BubbleSet mu eps).Finite ∧
      ((BubbleSet mu eps).ncard : ℝ≥0∞) * eps ≤ E := by
  -- Choose `k` with `E < k * eps`; no `k` points can all be bubbling points.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, E < (k : ℝ≥0∞) * eps := by
    rcases eq_or_ne eps ⊤ with rfl | -
    · exact ⟨1, by simpa using hE.lt_top⟩
    · obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt (r := E / eps) (ENNReal.div_lt_top hE heps).ne
      exact ⟨k, by rwa [ENNReal.div_lt_iff (Or.inl heps) (Or.inr hE)] at hk⟩
  have hfin : (BubbleSet mu eps).Finite := by
    by_contra hinf
    rw [Set.not_finite] at hinf
    obtain ⟨t, hts, htc⟩ := hinf.exists_subset_card_eq k
    have := finset_card_mul_le_of_subset_bubbleSet mu E eps hbound t hts
    rw [htc] at this
    exact absurd this (not_le.2 hk)
  refine ⟨hfin, ?_⟩
  have hsub : ((hfin.toFinset : Finset X) : Set X) ⊆ BubbleSet mu eps := by
    simp [Set.Finite.coe_toFinset]
  have := finset_card_mul_le_of_subset_bubbleSet mu E eps hbound hfin.toFinset hsub
  rwa [Set.ncard_eq_toFinset_card _ hfin]

/-- Energy-density form of the bubbling theorem.  If `F n : X → V` are curvature fields
(for instance the curvatures `F_{A_n}` of a sequence of connections) whose energies
`∫ ‖F n‖²` are bounded by `E`, then the set of points where at least `eps` of the energy
concentrates at all scales is finite, with at most `E / eps` points. -/
theorem uhlenbeck_bubbling_energy_density {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {V : Type*} [NormedAddCommGroup V]
    (vol : Measure X) (F : ℕ → X → V) (E eps : ℝ≥0∞) (hE : E ≠ ⊤) (heps : eps ≠ 0)
    (hbound : ∀ n, ∫⁻ x, ‖F n x‖ₑ ^ 2 ∂vol ≤ E) :
    (BubbleSet (fun n => vol.withDensity (fun x => ‖F n x‖ₑ ^ 2)) eps).Finite ∧
      ((BubbleSet (fun n => vol.withDensity (fun x => ‖F n x‖ₑ ^ 2)) eps).ncard : ℝ≥0∞) * eps
        ≤ E := by
  refine uhlenbeck_bubbling _ E eps hE heps (fun n => ?_)
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hbound n

end Frontier

