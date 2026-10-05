/-
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
# Uhlenbeck Bubbling

Concentration–compactness ("bubbling") for a sequence of Yang–Mills energy measures.

Uhlenbeck's compactness theorem is built on two pillars: an `ε`-regularity theorem (a
connection with small local curvature energy is, after a gauge change, controlled in
every Sobolev norm) and the *bubbling* mechanism, which says that a sequence of
connections with uniformly bounded Yang–Mills energy `Λ` can fail to have small local
energy only at **finitely many** points, at most `Λ / ε₀` of them, where `ε₀` is the
threshold of the `ε`-regularity theorem.

This file formalizes the second pillar in the generality in which it is actually used —
i.e. as a statement about the energy measures `μ n = |F_{A_n}|² dvol` alone — and proves
it: the bubbling set is finite, energy is quantized on it (`#bubbles · ε ≤ Λ`), and off
the bubbling set the small-energy hypothesis of `ε`-regularity is available on a fixed
ball along a subsequence.
-/

namespace Frontier

open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The **bubbling set** (energy concentration set) at level `ε` of a sequence of energy
measures `μ n`.

In the Yang–Mills setting `μ n` is the energy measure `|F_{A_n}|² dvol` of a sequence of
connections `A_n`, and `ε` is the `ε`-regularity threshold `ε₀` of Uhlenbeck's theorem.
A point `x` lies in the bubbling set when, at *every* scale `r > 0`, at least `ε` of the
energy asymptotically concentrates in the ball `B(x, r)`: these are exactly the points at
which a bubble can form, i.e. the points where `ε`-regularity may fail. -/
def bubbleSet (μ : ℕ → Measure X) (ε : ℝ≥0∞) : Set X :=
  {x : X | ∀ r : ℝ, 0 < r → ε ≤ liminf (fun n : ℕ => μ n (ball x r)) atTop}

omit [MeasurableSpace X] [BorelSpace X] in
/-- A finite set of points of a metric space can be surrounded by pairwise disjoint balls
of a common positive radius. -/
lemma exists_radius_pairwiseDisjoint_ball (s : Finset X) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint (ball x r) (ball y r) := by
  obtain ⟨C, hC, hCs⟩ := (s.finite_toSet).relatively_discrete
  set D : ℝ≥0∞ := min C 1 with hD
  have hD0 : D ≠ 0 := by simp [hD, hC.ne']
  have hDtop : D ≠ ⊤ := by simp [hD]
  have hpos : 0 < D.toReal := ENNReal.toReal_pos hD0 hDtop
  refine ⟨D.toReal / 2, by linarith, ?_⟩
  intro x hx y hy hxy
  refine Metric.ball_disjoint_ball ?_
  have h1 : D ≤ edist x y := le_trans (min_le_left _ _) (hCs x hx y hy hxy)
  have h2 : D.toReal ≤ dist x y := by
    have := ENNReal.toReal_mono (by simp [edist_dist]) h1
    simpa [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using this
  linarith

omit [BorelSpace X] in
/-- Off the bubbling set, the energy in some fixed small ball drops below the threshold `ε`
along a subsequence: this is precisely the hypothesis of Uhlenbeck's `ε`-regularity
theorem. -/
lemma frequently_lt_of_notMem_bubbleSet {μ : ℕ → Measure X} {ε : ℝ≥0∞} {x : X}
    (hx : x ∉ bubbleSet μ ε) :
    ∃ r : ℝ, 0 < r ∧ ∃ᶠ n : ℕ in atTop, μ n (ball x r) < ε := by
  simp only [bubbleSet, Set.mem_setOf_eq, not_forall, not_le] at hx
  obtain ⟨r, hr, hlt⟩ := hx
  exact ⟨r, hr, frequently_lt_of_liminf_lt (by isBoundedDefault) hlt⟩

/-- **Energy quantization on finite subsets.**  Any finite set of bubbling points carries at
least `ε` of energy each, hence its cardinality is controlled by the total energy `Λ`. -/
lemma card_mul_le_of_subset_bubbleSet {μ : ℕ → Measure X} {Λ ε : ℝ≥0∞}
    (hbound : ∀ n : ℕ, μ n Set.univ ≤ Λ) (s : Finset X) (hs : ↑s ⊆ bubbleSet μ ε) :
    (s.card : ℝ≥0∞) * ε ≤ Λ := by
  obtain ⟨r, hr, hdisj⟩ := exists_radius_pairwiseDisjoint_ball s
  have hdisj' : (↑s : Set X).PairwiseDisjoint (fun x : X => ball x r) := by
    intro x hx y hy hxy
    exact hdisj x hx y hy hxy
  -- Every level `c < ε` is achieved simultaneously at all the points of `s`, at some
  -- common index `n`; the corresponding balls are disjoint, so `s.card * c ≤ Λ`.
  have key : ∀ c : ℝ≥0∞, c < ε → (s.card : ℝ≥0∞) * c ≤ Λ := by
    intro c hc
    have hev : ∀ᶠ n : ℕ in atTop, ∀ x ∈ s, c < μ n (ball x r) := by
      rw [eventually_all_finset]
      intro x hx
      exact eventually_lt_of_lt_liminf (lt_of_lt_of_le hc (hs hx r hr))
    obtain ⟨n, hn⟩ := hev.exists
    calc (s.card : ℝ≥0∞) * c = ∑ _x ∈ s, c := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ s, μ n (ball x r) := Finset.sum_le_sum (fun x hx => (hn x hx).le)
      _ = μ n (⋃ x ∈ s, ball x r) :=
          (measure_biUnion_finset hdisj' (fun x _ => measurableSet_ball)).symm
      _ ≤ μ n Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ Λ := hbound n
  -- Passing to the supremum over `c < ε`.
  by_contra hcon
  push_neg at hcon
  have hN : (s.card : ℝ≥0∞) ≠ 0 := by
    rintro h
    rw [h, zero_mul] at hcon
    exact (not_lt_of_ge (zero_le Λ)) hcon
  have hNtop : (s.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h1 : Λ / (s.card : ℝ≥0∞) < ε := by
    rw [ENNReal.div_lt_iff (Or.inl hN) (Or.inl hNtop)]
    simpa [mul_comm] using hcon
  obtain ⟨c, hc1, hc2⟩ := exists_between h1
  have hkey := key c hc2
  rw [ENNReal.div_lt_iff (Or.inl hN) (Or.inl hNtop)] at hc1
  rw [mul_comm] at hkey
  exact absurd hkey (not_le_of_gt hc1)

/-- The bubbling set of a sequence of energy measures of uniformly bounded total energy is
finite. -/
lemma finite_bubbleSet {μ : ℕ → Measure X} {Λ ε : ℝ≥0∞} (hΛ : Λ ≠ ⊤) (hε : ε ≠ 0)
    (hbound : ∀ n : ℕ, μ n Set.univ ≤ Λ) :
    (bubbleSet μ ε).Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt (ENNReal.div_lt_top hΛ hε).ne
  obtain ⟨t, hts, htc⟩ := hinf.exists_subset_card_eq k
  have hle := card_mul_le_of_subset_bubbleSet hbound t hts
  rw [htc] at hle
  rw [ENNReal.div_lt_iff (Or.inl hε) (Or.inr hΛ)] at hk
  exact absurd hle (not_le_of_gt hk)

/-- **Uhlenbeck bubbling / concentration–compactness for Yang–Mills energies.**

Let `μ n` be the energy measures `|F_{A_n}|² dvol` of a sequence of connections with
uniformly bounded Yang–Mills energy `Λ < ∞`, and let `ε > 0` be the `ε`-regularity
threshold of Uhlenbeck's theorem.  Then:

* the bubbling set (the set of points where at least `ε` of energy concentrates at every
  scale) is **finite**;
* its cardinality is bounded by `Λ / ε`, in the quantized form `#bubbles · ε ≤ Λ`;
* at every point *outside* the bubbling set there is a fixed ball on which, along a
  subsequence, the energy stays below the threshold `ε` — the small-energy hypothesis
  from which Uhlenbeck's `ε`-regularity yields local convergence (after gauge change)
  away from the finitely many bubble points. -/
theorem uhlenbeck_bubbling {μ : ℕ → Measure X} {Λ ε : ℝ≥0∞} (hΛ : Λ ≠ ⊤) (hε : ε ≠ 0)
    (hbound : ∀ n : ℕ, μ n Set.univ ≤ Λ) :
    (bubbleSet μ ε).Finite ∧
      ((bubbleSet μ ε).ncard : ℝ≥0∞) * ε ≤ Λ ∧
      ∀ x ∉ bubbleSet μ ε, ∃ r : ℝ, 0 < r ∧ ∃ᶠ n : ℕ in atTop, μ n (ball x r) < ε := by
  have hfin : (bubbleSet μ ε).Finite := finite_bubbleSet hΛ hε hbound
  refine ⟨hfin, ?_, fun x hx => frequently_lt_of_notMem_bubbleSet hx⟩
  have h := card_mul_le_of_subset_bubbleSet (ε := ε) hbound hfin.toFinset
    (by rw [Set.Finite.coe_toFinset])
  rwa [Set.ncard_eq_toFinset_card _ hfin]

/-- Non-vacuity of `Frontier.bubbleSet`: a sequence of energy measures all of whose energy
sits at a single point `x₀` (the model case of a bubble) has bubbling set exactly `{x₀}`,
realizing the bound `#bubbles · ε ≤ Λ` with `ε = Λ = 1`. -/
lemma bubbleSet_dirac (x₀ : X) : bubbleSet (fun _ : ℕ => Measure.dirac x₀) 1 = {x₀} := by
  ext x
  simp only [bubbleSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    have hr : 0 < dist x x₀ := dist_pos.2 hne
    have hthis := h (dist x x₀) hr
    have hmeas : (Measure.dirac x₀) (ball x (dist x x₀)) = 0 := by
      rw [MeasureTheory.Measure.dirac_apply' _ measurableSet_ball]
      simp [Metric.mem_ball, dist_comm]
    simp [hmeas] at hthis
  · rintro rfl
    intro r hr
    have hmeas : (Measure.dirac x) (ball x r) = 1 := by
      rw [MeasureTheory.Measure.dirac_apply' _ measurableSet_ball]
      simp [Metric.mem_ball, hr]
    simp [hmeas]

/-- The bubbling set of a sequence of energy *densities* `e n` (in Yang–Mills: the
pointwise curvature densities `|F_{A_n}|²`) with respect to a background volume measure
`vol`: the points where, at every scale, at least `ε` of the energy `∫ |F_{A_n}|²`
asymptotically concentrates. -/
def bubbleSetDensity (vol : Measure X) (e : ℕ → X → ℝ≥0∞) (ε : ℝ≥0∞) : Set X :=
  {x : X | ∀ r : ℝ, 0 < r → ε ≤ liminf (fun n : ℕ => ∫⁻ y in ball x r, e n y ∂vol) atTop}

/-- **Uhlenbeck bubbling, energy-density form.**  For a sequence of curvature energy
densities `e n = |F_{A_n}|²` with uniformly bounded total Yang–Mills energy
`∫ |F_{A_n}|² dvol ≤ Λ < ∞`, the bubbling set is finite and carries at most `Λ / ε`
bubbles. -/
theorem uhlenbeck_bubbling_density {vol : Measure X} {e : ℕ → X → ℝ≥0∞}
    {Λ ε : ℝ≥0∞} (hΛ : Λ ≠ ⊤) (hε : ε ≠ 0)
    (hbound : ∀ n : ℕ, ∫⁻ y, e n y ∂vol ≤ Λ) :
    (bubbleSetDensity vol e ε).Finite ∧
      ((bubbleSetDensity vol e ε).ncard : ℝ≥0∞) * ε ≤ Λ := by
  set μ : ℕ → Measure X := fun n => vol.withDensity (e n) with hμ
  have happly : ∀ (n : ℕ) (s : Set X), MeasurableSet s → μ n s = ∫⁻ y in s, e n y ∂vol :=
    fun n s hs => withDensity_apply (e n) hs
  have hbound' : ∀ n : ℕ, μ n Set.univ ≤ Λ := by
    intro n
    rw [happly n _ MeasurableSet.univ, Measure.restrict_univ]
    exact hbound n
  have hset : bubbleSetDensity vol e ε = bubbleSet μ ε := by
    ext x
    simp only [bubbleSetDensity, bubbleSet, Set.mem_setOf_eq]
    refine forall_congr' fun r => ?_
    refine imp_congr_right fun _ => ?_
    simp only [happly _ _ measurableSet_ball]
  obtain ⟨h1, h2, -⟩ := uhlenbeck_bubbling (μ := μ) hΛ hε hbound'
  exact ⟨hset ▸ h1, hset ▸ h2⟩

end Frontier

