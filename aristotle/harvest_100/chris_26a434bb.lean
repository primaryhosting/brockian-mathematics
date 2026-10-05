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
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open MeasureTheory Filter Metric Set

/-- A point `x` is an *energy concentration point* (a *bubble point*) at level `eps`
for a sequence of energy measures `mu n` (think: `mu n = |F_{A n}|² dvol`, the Yang–Mills
energy density of a sequence of connections `A n`) if on *every* ball around `x` the
asymptotic energy is at least `eps`. -/
def BubblePoint {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (mu : ℕ → Measure X) (eps : ℝ≥0∞) (x : X) : Prop :=
  ∀ r : ℝ, 0 < r → eps ≤ liminf (fun n => mu n (Metric.ball x r)) atTop

/-- The set of bubble points ("blow-up set") of a sequence of energy measures. -/
def BubbleSet {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (mu : ℕ → Measure X) (eps : ℝ≥0∞) : Set X :=
  {x | BubblePoint mu eps x}

/-- Finitely many distinct points of a metric space can be surrounded by pairwise
disjoint balls of a common positive radius. -/
theorem exists_pos_pairwiseDisjoint_balls {X : Type*} [MetricSpace X] (S : Finset X) :
    ∃ r : ℝ, 0 < r ∧ (↑S : Set X).PairwiseDisjoint (fun x => Metric.ball x r) := by
  classical
  set T : Finset ℝ :=
    insert 1 (((S ×ˢ S).filter fun p => p.1 ≠ p.2).image fun p => dist p.1 p.2) with hT
  have hTne : T.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have hm : 0 < T.min' hTne := by
    rw [Finset.lt_min'_iff]
    intro b hb
    rw [hT, Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · norm_num
    · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hb
      obtain ⟨p, ⟨-, hne⟩, rfl⟩ := hb
      exact dist_pos.2 hne
  refine ⟨T.min' hTne / 2, by positivity, ?_⟩
  intro x hx y hy hxy
  have hxy' : T.min' hTne ≤ dist x y := by
    refine Finset.min'_le _ _ ?_
    rw [hT, Finset.mem_insert]
    right
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product]
    exact ⟨(x, y), ⟨⟨hx, hy⟩, hxy⟩, rfl⟩
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro z hz hz'
  simp only [Metric.mem_ball] at hz hz'
  rw [dist_comm] at hz
  have htri : dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
  linarith

/-- Multiplication by a natural number in `ℝ≥0∞` is controlled by its values strictly
below the threshold: a limiting form of `k * x ≤ y`. -/
theorem nat_mul_le_of_forall_lt (k : ℕ) (x y : ℝ≥0∞) (h : ∀ c < x, (k : ℝ≥0∞) * c ≤ y) :
    (k : ℝ≥0∞) * x ≤ y := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rcases eq_or_ne y ⊤ with rfl | hy
  · simp
  by_contra hcon
  push_neg at hcon
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  have hkt : (k : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top k
  have hlt : y / (k : ℝ≥0∞) < x := by
    rw [ENNReal.div_lt_iff (Or.inl hk0) (Or.inl hkt)]
    rwa [mul_comm] at hcon
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  have hle := h c hc2
  have hmul : y < (k : ℝ≥0∞) * c := by
    calc y = (k : ℝ≥0∞) * (y / k) := (ENNReal.mul_div_cancel hk0 hkt).symm
      _ < (k : ℝ≥0∞) * c := ENNReal.mul_lt_mul_right hk0 hkt hc1
  exact absurd hle (not_le.2 hmul)

/-- **Energy counting bound.** Any finite set of bubble points at level `eps` for a
sequence of energy measures of total mass at most `Lam` satisfies `#S * eps ≤ Lam`. -/
theorem finset_card_mul_le_of_bubble {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (mu : ℕ → Measure X) (Lam eps : ℝ≥0∞)
    (hbound : ∀ n, mu n Set.univ ≤ Lam) (S : Finset X)
    (hS : ∀ x ∈ S, BubblePoint mu eps x) :
    (S.card : ℝ≥0∞) * eps ≤ Lam := by
  refine nat_mul_le_of_forall_lt _ _ _ ?_
  intro c hc
  obtain ⟨r, hr, hdisj⟩ := exists_pos_pairwiseDisjoint_balls S
  have hev : ∀ x ∈ S, ∀ᶠ n in atTop, c < mu n (Metric.ball x r) := fun x hx =>
    eventually_lt_of_lt_liminf (lt_of_lt_of_le hc (hS x hx r hr))
  have hall : ∀ᶠ n in atTop, ∀ x ∈ S, c < mu n (Metric.ball x r) :=
    (Filter.eventually_all_finset S).2 hev
  obtain ⟨n, hn⟩ := hall.exists
  calc (S.card : ℝ≥0∞) * c = ∑ _x ∈ S, c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ S, mu n (Metric.ball x r) := Finset.sum_le_sum fun x hx => (hn x hx).le
    _ = mu n (⋃ x ∈ S, Metric.ball x r) :=
        (measure_biUnion_finset hdisj fun _ _ => measurableSet_ball).symm
    _ ≤ mu n Set.univ := measure_mono (Set.subset_univ _)
    _ ≤ Lam := hbound n

/-- The blow-up set is finite whenever the energies are uniformly bounded by a finite
`Lam` and the concentration level `eps` is positive. -/
theorem bubbleSet_finite {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (mu : ℕ → Measure X) (Lam eps : ℝ≥0∞)
    (hLam : Lam ≠ ⊤) (heps : eps ≠ 0) (hbound : ∀ n, mu n Set.univ ≤ Lam) :
    (BubbleSet mu eps).Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  set e : ℝ≥0∞ := min eps 1 with he
  have he0 : e ≠ 0 := by simp [he, heps]
  have het : e ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (min_le_right _ _)
  have hdiv : Lam / e ≠ ⊤ := (ENNReal.div_lt_top hLam he0).ne
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hdiv
  obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq k
  have hbub : ∀ x ∈ T, BubblePoint mu e x := by
    intro x hx r hr
    exact le_trans (min_le_left _ _) (hTsub hx r hr)
  have hle := finset_card_mul_le_of_bubble mu Lam e hbound T hbub
  rw [hTcard] at hle
  have hgt : Lam < (k : ℝ≥0∞) * e := by
    calc Lam = (Lam / e) * e := (ENNReal.div_mul_cancel he0 het).symm
      _ < (k : ℝ≥0∞) * e := by
          rw [mul_comm (Lam / e) e, mul_comm ((k : ℝ≥0∞)) e]
          exact ENNReal.mul_lt_mul_right he0 het hk
  exact absurd hle (not_le.2 hgt)

/-- **Uhlenbeck bubbling (energy concentration base case).**

Let `mu n` be the Yang–Mills energy densities of a sequence of connections, with
uniformly bounded total energy `mu n univ ≤ Lam < ∞`, and let `eps > 0` be an energy
quantum (the Uhlenbeck `eps`-regularity threshold). Then:

* the blow-up set of points where at least `eps` of energy concentrates is **finite**;
* its cardinality obeys the counting bound `#bubbles * eps ≤ Lam`, i.e. at most
  `Lam / eps` bubbles can form;
* away from the blow-up set, energy does **not** concentrate: every other point has a
  ball on which, along a subsequence, the energy stays below `eps` (the situation in
  which `eps`-regularity applies and the singularity is removable). -/
theorem uhlenbeck_bubbling {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (mu : ℕ → Measure X) (Lam eps : ℝ≥0∞)
    (hLam : Lam ≠ ⊤) (heps : eps ≠ 0) (hbound : ∀ n, mu n Set.univ ≤ Lam) :
    (BubbleSet mu eps).Finite ∧
      ((BubbleSet mu eps).ncard : ℝ≥0∞) * eps ≤ Lam ∧
      ∀ x ∉ BubbleSet mu eps, ∃ r : ℝ, 0 < r ∧
        ∃ᶠ n in atTop, mu n (Metric.ball x r) < eps := by
  have hfin : (BubbleSet mu eps).Finite := bubbleSet_finite mu Lam eps hLam heps hbound
  refine ⟨hfin, ?_, ?_⟩
  · have hcard := finset_card_mul_le_of_bubble mu Lam eps hbound hfin.toFinset
      fun x hx => hfin.mem_toFinset.1 hx
    rwa [← Set.ncard_eq_toFinset_card _ hfin] at hcard
  · intro x hx
    simp only [BubbleSet, Set.mem_setOf_eq, BubblePoint, not_forall] at hx
    obtain ⟨r, hr, hlt⟩ := hx
    exact ⟨r, hr, frequently_lt_of_liminf_lt (by isBoundedDefault) (not_le.1 hlt)⟩

/-- **Non-vacuity / sharpness.** A genuinely bubbling sequence: unit Dirac masses at the
origin (the model of an energy quantum concentrating at a point) have blow-up set exactly
`{0}` at level `1`, and the counting bound of `uhlenbeck_bubbling` is attained there
(`1 * 1 ≤ 1`). -/
theorem bubbleSet_dirac : BubbleSet (fun _ : ℕ => Measure.dirac (0 : ℝ)) 1 = {0} := by
  ext x
  simp only [BubbleSet, Set.mem_setOf_eq, BubblePoint, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hx
    have habs : 0 < |x| := abs_pos.2 hx
    have hr : 0 < |x| / 2 := by linarith
    have hmem : (0 : ℝ) ∉ Metric.ball x (|x| / 2) := by
      simp only [Metric.mem_ball, Real.dist_eq, not_lt]
      rw [zero_sub, abs_neg]
      linarith
    have h0 : Measure.dirac (0 : ℝ) (Metric.ball x (|x| / 2)) = 0 := by
      rw [Measure.dirac_apply' _ measurableSet_ball]
      exact Set.indicator_of_notMem hmem 1
    have hcon := h (|x| / 2) hr
    simp only [h0] at hcon
    simp at hcon
  · rintro rfl r hr
    have h1 : Measure.dirac (0 : ℝ) (Metric.ball (0 : ℝ) r) = 1 := by
      rw [Measure.dirac_apply' _ measurableSet_ball]
      exact Set.indicator_of_mem (Metric.mem_ball_self hr) 1
    simp [h1]

end Frontier

