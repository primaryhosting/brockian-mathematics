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
open scoped Topology

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

open MeasureTheory Metric Set Filter

namespace Frontier

/-!
## Setting

For a sequence of Yang–Mills connections `A i` on a bundle over a Riemannian manifold `X`
with uniformly bounded energy, the energy densities `|F_{A i}|² dvol` form a sequence of
Borel measures on `X` with uniformly bounded total mass.  Uhlenbeck's theory says:

* (ε-regularity)  there is an energy quantum `ε₀ > 0` such that if the energy in some ball
  around `x` is `< ε₀`, then the convergence is smooth up to gauge near `x` and the
  singularity there is removable;
* (bubbling)  consequently the set of points at which the convergence fails is contained in
  the *concentration set*, which is a finite set with at most `(total energy)/ε₀` points:
  energy concentrates ("bubbles off") at finitely many points only.

The development below formalizes and proves the measure-theoretic core of this picture, in
two forms.

* `Frontier.uhlenbeck_bubbling`: for the limiting energy measure `μ` (of finite total
  energy) and a positive energy quantum `ε₀`, the bubbling set is closed and finite, the
  number of bubble points satisfies `#(bubble points) · ε₀ ≤ total energy`, and — given
  ε-regularity as a hypothesis — every point off the bubbling set is a regular point.
  This is exactly the reduction of Uhlenbeck bubbling to the local ε-regularity theorem.

* `Frontier.uhlenbeck_bubbling_sequence`: the same conclusions directly along a *sequence*
  of energy measures with uniformly bounded total energy `E`, where the bubbling set is
  defined through the lower limit of the energy in small balls; no weak limit of measures
  needs to be extracted.  (The lower limit is the correct notion here: with the upper limit
  the statement is false, since energy may oscillate between two points along a sequence.)

The two remaining analytic inputs of Uhlenbeck's theorem — the local ε-regularity /
removable singularity theorem and Uhlenbeck's gauge fixing — enter as the hypothesis `hreg`.
-/

/-! ## Auxiliary arithmetic and disjointness lemmas -/

/-- For a finite bound `E` and a positive quantum `ε₀`, some multiple `n • ε₀` exceeds `E`. -/
theorem exists_nat_mul_gt {E ε₀ : ℝ≥0∞} (hE : E ≠ ⊤) (hε₀ : 0 < ε₀) :
    ∃ n : ℕ, E < (n : ℝ≥0∞) * ε₀ := by
  by_cases htop : ε₀ = ⊤
  · exact ⟨1, by rw [Nat.cast_one, one_mul, htop]; exact lt_top_iff_ne_top.mpr hE⟩
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hE hε₀.ne')
    exact ⟨n, by rwa [ENNReal.div_lt_iff (Or.inl hε₀.ne') (Or.inl htop)] at hn⟩

/-- Superadditivity of `liminf` for two `ℝ≥0∞`-valued sequences. -/
theorem add_liminf_le_liminf_add (u v : ℕ → ℝ≥0∞) :
    liminf u atTop + liminf v atTop ≤ liminf (fun n : ℕ => u n + v n) atTop := by
  rw [liminf_eq_iSup_iInf_of_nat, liminf_eq_iSup_iInf_of_nat, liminf_eq_iSup_iInf_of_nat]
  have hmonoU : Monotone (fun n : ℕ => ⨅ i ≥ n, u i) := fun a b hab =>
    le_iInf₂ fun i hi => iInf₂_le i (le_trans hab hi)
  have hmonoV : Monotone (fun n : ℕ => ⨅ i ≥ n, v i) := fun a b hab =>
    le_iInf₂ fun i hi => iInf₂_le i (le_trans hab hi)
  rw [ENNReal.iSup_add_iSup (fun i j => ⟨max i j,
    add_le_add (hmonoU (le_max_left i j)) (hmonoV (le_max_right i j))⟩)]
  exact iSup_mono fun n => le_iInf₂ fun i hi => add_le_add (iInf₂_le i hi) (iInf₂_le i hi)

/-- Superadditivity of `liminf` for a finite family of `ℝ≥0∞`-valued sequences. -/
theorem sum_liminf_le_liminf_sum {ι : Type*} (s : Finset ι) (u : ι → ℕ → ℝ≥0∞) :
    ∑ x ∈ s, liminf (u x) atTop ≤ liminf (fun n : ℕ => ∑ x ∈ s, u x n) atTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hcongr : liminf (fun n : ℕ => ∑ x ∈ insert a s, u x n) atTop
          = liminf (fun n : ℕ => u a n + ∑ x ∈ s, u x n) atTop := by
        refine liminf_congr ?_
        filter_upwards with n
        rw [Finset.sum_insert ha]
      rw [Finset.sum_insert ha, hcongr]
      exact le_trans (add_le_add le_rfl ih) (add_liminf_le_liminf_add _ _)

/-- A finite set of points admits a positive radius making the balls around them pairwise
disjoint. -/
theorem exists_radius_pairwiseDisjoint {X : Type*} [MetricSpace X] (s : Finset X) :
    ∃ r : ℝ, 0 < r ∧ (↑s : Set X).PairwiseDisjoint (fun x : X => Metric.ball x r) := by
  classical
  set D : Finset ℝ := s.offDiag.image (fun p : X × X => dist p.1 p.2) with hD
  by_cases hne : D.Nonempty
  · refine ⟨D.min' hne / 2, ?_, ?_⟩
    · obtain ⟨p, hp, hpd⟩ := Finset.mem_image.mp (D.min'_mem hne)
      rw [Finset.mem_offDiag] at hp
      have hpos : 0 < dist p.1 p.2 := dist_pos.2 hp.2.2
      rw [hpd] at hpos
      linarith
    · intro x hx y hy hxy
      have hdxy : D.min' hne ≤ dist x y := by
        apply Finset.min'_le
        rw [hD, Finset.mem_image]
        exact ⟨(x, y), Finset.mem_offDiag.2 ⟨hx, hy, hxy⟩, rfl⟩
      simp only [Function.onFun]
      rw [Set.disjoint_left]
      rintro z hz hz'
      rw [Metric.mem_ball, dist_comm] at hz hz'
      have htri := dist_triangle x z y
      rw [dist_comm z y] at htri
      linarith
  · refine ⟨1, one_pos, ?_⟩
    intro x hx y hy hxy
    exfalso
    refine hne ⟨dist x y, ?_⟩
    rw [hD, Finset.mem_image]
    exact ⟨(x, y), Finset.mem_offDiag.2 ⟨hx, hy, hxy⟩, rfl⟩

/-! ## The bubbling set of a limiting energy measure -/

/-- The **bubbling (concentration) set** of a measure `μ` at energy threshold `ε₀`:
the points at which every ball carries at least `ε₀` of the energy.  For the limit of a
sequence of Yang–Mills connections these are exactly the points where a bubble can form. -/
def bubbleSet {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (ε₀ : ℝ≥0∞) : Set X :=
  {x : X | ∀ r : ℝ, 0 < r → ε₀ ≤ μ (Metric.ball x r)}

/-- Points outside the bubbling set carry small energy in some ball: this is precisely the
hypothesis of the ε-regularity theorem. -/
theorem exists_ball_measure_lt_of_notMem_bubbleSet {X : Type*} [MetricSpace X]
    [MeasurableSpace X] {μ : Measure X} {ε₀ : ℝ≥0∞} {x : X} (hx : x ∉ bubbleSet μ ε₀) :
    ∃ r : ℝ, 0 < r ∧ μ (Metric.ball x r) < ε₀ := by
  simp only [bubbleSet, Set.mem_setOf_eq, not_forall, not_le] at hx
  obtain ⟨r, hr, hlt⟩ := hx
  exact ⟨r, hr, hlt⟩

/-- **Energy quantization bound.**  Any finite set of bubble points has cardinality at most
the total energy divided by the energy quantum. -/
theorem card_mul_le_measure_univ {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) (ε₀ : ℝ≥0∞) (s : Finset X)
    (hs : (↑s : Set X) ⊆ bubbleSet μ ε₀) :
    (s.card : ℝ≥0∞) * ε₀ ≤ μ Set.univ := by
  obtain ⟨r, hr, hdisj⟩ := exists_radius_pairwiseDisjoint s
  have hsum : μ (⋃ x ∈ s, Metric.ball x r) = ∑ x ∈ s, μ (Metric.ball x r) :=
    measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)
  calc (s.card : ℝ≥0∞) * ε₀ = ∑ _x ∈ s, ε₀ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ s, μ (Metric.ball x r) :=
        Finset.sum_le_sum (fun x hx => hs (by exact_mod_cast hx) r hr)
    _ = μ (⋃ x ∈ s, Metric.ball x r) := hsum.symm
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)

/-- The bubbling set of a finite measure is finite. -/
theorem bubbleSet_finite {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {ε₀ : ℝ≥0∞}
    (hε₀ : 0 < ε₀) : (bubbleSet μ ε₀).Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨n, hn⟩ := exists_nat_mul_gt (measure_ne_top μ Set.univ) hε₀
  obtain ⟨t, hts, htcard⟩ := hinf.exists_subset_card_eq n
  have hbound := card_mul_le_measure_univ μ ε₀ t hts
  rw [htcard] at hbound
  exact absurd hbound (not_le.mpr hn)

/-- The bubbling set is closed. -/
theorem bubbleSet_isClosed {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (ε₀ : ℝ≥0∞) : IsClosed (bubbleSet μ ε₀) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro x hx
  simp only [Set.mem_compl_iff, bubbleSet, Set.mem_setOf_eq, not_forall, not_le] at hx
  obtain ⟨r, hr, hlt⟩ := hx
  refine ⟨r / 2, by linarith, ?_⟩
  intro y hy
  rw [Metric.mem_ball] at hy
  simp only [Set.mem_compl_iff, bubbleSet, Set.mem_setOf_eq, not_forall, not_le]
  refine ⟨r / 2, by linarith, ?_⟩
  have hsub : Metric.ball y (r / 2) ⊆ Metric.ball x r :=
    Metric.ball_subset_ball' (by linarith)
  exact lt_of_le_of_lt (measure_mono hsub) hlt

/-- Cardinality bound for the (finite) bubbling set: the number of bubbles times the energy
quantum is at most the total energy. -/
theorem bubbleSet_ncard_mul_le {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {ε₀ : ℝ≥0∞}
    (hε₀ : 0 < ε₀) :
    ((bubbleSet μ ε₀).ncard : ℝ≥0∞) * ε₀ ≤ μ Set.univ := by
  have hfin : (bubbleSet μ ε₀).Finite := bubbleSet_finite μ hε₀
  have hcard : (bubbleSet μ ε₀).ncard = hfin.toFinset.card := Set.ncard_eq_toFinset_card _ hfin
  rw [hcard]
  refine card_mul_le_measure_univ μ ε₀ hfin.toFinset ?_
  intro x hx
  simpa using hx

/-! ## Uhlenbeck bubbling -/

/-- **Uhlenbeck bubbling.**

Let `μ` be the limiting energy measure (`|F_A|² dvol`) of a sequence of Yang–Mills
connections over a metric measure space `X`, of finite total energy, and let `ε₀ > 0` be the
energy quantum supplied by the ε-regularity theorem, encoded here by the hypothesis `hreg`:
a point having less than `ε₀` energy in some ball around it is a regular point (the
singularity there is removable and the convergence is smooth up to gauge nearby).

Then energy concentrates at only finitely many points: the *bubbling set* is closed and
finite, the number of bubbles is bounded by the total energy divided by `ε₀`, and every
point off the bubbling set is regular. -/
theorem uhlenbeck_bubbling {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {ε₀ : ℝ≥0∞}
    (hε₀ : 0 < ε₀) (Reg : X → Prop)
    (hreg : ∀ x : X, (∃ r : ℝ, 0 < r ∧ μ (Metric.ball x r) < ε₀) → Reg x) :
    IsClosed (bubbleSet μ ε₀) ∧
      (bubbleSet μ ε₀).Finite ∧
      ((bubbleSet μ ε₀).ncard : ℝ≥0∞) * ε₀ ≤ μ Set.univ ∧
      (∀ x : X, x ∉ bubbleSet μ ε₀ → Reg x) :=
  ⟨bubbleSet_isClosed μ ε₀, bubbleSet_finite μ hε₀, bubbleSet_ncard_mul_le μ hε₀,
    fun x hx => hreg x (exists_ball_measure_lt_of_notMem_bubbleSet hx)⟩

/-! ## Bubbling along a sequence of connections

The version above concerns the limiting energy measure.  We now give the version along a
sequence `μ 0, μ 1, …` of energy measures with uniformly bounded total energy `E`, with no
limit measure extracted; the concentration set is defined using the lower limit of the
energy in small balls. -/

/-- The **bubbling set of a sequence** of energy measures at threshold `ε₀`: points where the
lower limit of the energy in every ball is at least `ε₀`. -/
def seqBubbleSet {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : ℕ → Measure X) (ε₀ : ℝ≥0∞) : Set X :=
  {x : X | ∀ r : ℝ, 0 < r → ε₀ ≤ liminf (fun n : ℕ => μ n (Metric.ball x r)) atTop}

/-- Energy quantization along a sequence: a finite set of bubble points of a sequence of
measures of total energy at most `E` has at most `E / ε₀` elements. -/
theorem seq_card_mul_le {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : ℕ → Measure X) (ε₀ E : ℝ≥0∞)
    (hE : ∀ n : ℕ, μ n Set.univ ≤ E) (s : Finset X)
    (hs : (↑s : Set X) ⊆ seqBubbleSet μ ε₀) :
    (s.card : ℝ≥0∞) * ε₀ ≤ E := by
  obtain ⟨r, hr, hdisj⟩ := exists_radius_pairwiseDisjoint s
  have hsum : ∀ n : ℕ, ∑ x ∈ s, μ n (Metric.ball x r) = μ n (⋃ x ∈ s, Metric.ball x r) :=
    fun n => (measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)).symm
  calc (s.card : ℝ≥0∞) * ε₀ = ∑ _x ∈ s, ε₀ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ s, liminf (fun n : ℕ => μ n (Metric.ball x r)) atTop :=
        Finset.sum_le_sum (fun x hx => hs (by exact_mod_cast hx) r hr)
    _ ≤ liminf (fun n : ℕ => ∑ x ∈ s, μ n (Metric.ball x r)) atTop :=
        sum_liminf_le_liminf_sum s _
    _ ≤ liminf (fun _ : ℕ => E) atTop := by
        refine liminf_le_liminf ?_
        filter_upwards with n
        rw [hsum n]
        exact le_trans (measure_mono (Set.subset_univ _)) (hE n)
    _ = E := liminf_const E

/-- The bubbling set of a sequence of uniformly bounded energy measures is finite. -/
theorem seqBubbleSet_finite {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : ℕ → Measure X) {ε₀ E : ℝ≥0∞} (hε₀ : 0 < ε₀) (hEtop : E ≠ ⊤)
    (hE : ∀ n : ℕ, μ n Set.univ ≤ E) : (seqBubbleSet μ ε₀).Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨n, hn⟩ := exists_nat_mul_gt hEtop hε₀
  obtain ⟨t, hts, htcard⟩ := hinf.exists_subset_card_eq n
  have hbound := seq_card_mul_le μ ε₀ E hE t hts
  rw [htcard] at hbound
  exact absurd hbound (not_le.mpr hn)

/-- The bubbling set of a sequence is closed. -/
theorem seqBubbleSet_isClosed {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : ℕ → Measure X) (ε₀ : ℝ≥0∞) : IsClosed (seqBubbleSet μ ε₀) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro x hx
  simp only [Set.mem_compl_iff, seqBubbleSet, Set.mem_setOf_eq, not_forall, not_le] at hx
  obtain ⟨r, hr, hlt⟩ := hx
  refine ⟨r / 2, by linarith, ?_⟩
  intro y hy
  rw [Metric.mem_ball] at hy
  simp only [Set.mem_compl_iff, seqBubbleSet, Set.mem_setOf_eq, not_forall, not_le]
  refine ⟨r / 2, by linarith, ?_⟩
  have hsub : Metric.ball y (r / 2) ⊆ Metric.ball x r :=
    Metric.ball_subset_ball' (by linarith)
  refine lt_of_le_of_lt (liminf_le_liminf ?_) hlt
  filter_upwards with n
  exact measure_mono hsub

/-- **Uhlenbeck bubbling along a sequence.**

Given a sequence of energy measures `μ n` (the energy densities `|F_{A n}|² dvol` of a
sequence of Yang–Mills connections) with uniformly bounded total energy `E < ∞`, and an
energy quantum `ε₀ > 0` for which ε-regularity holds (hypothesis `hreg`), the set of points
at which energy concentrates along the sequence is closed and finite, has at most `E / ε₀`
elements, and every point outside of it is regular. -/
theorem uhlenbeck_bubbling_sequence {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : ℕ → Measure X) {ε₀ E : ℝ≥0∞} (hε₀ : 0 < ε₀) (hEtop : E ≠ ⊤)
    (hE : ∀ n : ℕ, μ n Set.univ ≤ E) (Reg : X → Prop)
    (hreg : ∀ x : X,
      (∃ r : ℝ, 0 < r ∧ liminf (fun n : ℕ => μ n (Metric.ball x r)) atTop < ε₀) → Reg x) :
    IsClosed (seqBubbleSet μ ε₀) ∧
      (seqBubbleSet μ ε₀).Finite ∧
      ((seqBubbleSet μ ε₀).ncard : ℝ≥0∞) * ε₀ ≤ E ∧
      (∀ x : X, x ∉ seqBubbleSet μ ε₀ → Reg x) := by
  have hfin : (seqBubbleSet μ ε₀).Finite := seqBubbleSet_finite μ hε₀ hEtop hE
  refine ⟨seqBubbleSet_isClosed μ ε₀, hfin, ?_, ?_⟩
  · have hcard : (seqBubbleSet μ ε₀).ncard = hfin.toFinset.card :=
      Set.ncard_eq_toFinset_card _ hfin
    rw [hcard]
    refine seq_card_mul_le μ ε₀ E hE hfin.toFinset ?_
    intro x hx
    simpa using hx
  · intro x hx
    simp only [seqBubbleSet, Set.mem_setOf_eq, not_forall, not_le] at hx
    obtain ⟨r, hr, hlt⟩ := hx
    exact hreg x ⟨r, hr, hlt⟩

/-! ## A concrete instance: energy densities on Euclidean space

The Yang–Mills energy measure on `ℝ⁴` is `|F_A|² dvol`, i.e. the volume measure weighted by a
nonnegative density of finite total integral.  For any such density, bubbling holds. -/

/-- Uhlenbeck bubbling for a Yang–Mills energy density `f` (think of `f = |F_A|²`) of finite
total energy on Euclidean space: the bubbling set is closed, finite, and its cardinality is
bounded by the total energy divided by the energy quantum. -/
theorem uhlenbeck_bubbling_energyDensity {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hfin : ∫⁻ x : EuclideanSpace ℝ (Fin d), f x ≠ ⊤) {ε₀ : ℝ≥0∞}
    (hε₀ : 0 < ε₀) :
    IsClosed (bubbleSet (volume.withDensity f) ε₀) ∧
      (bubbleSet (volume.withDensity f) ε₀).Finite ∧
      ((bubbleSet (volume.withDensity f) ε₀).ncard : ℝ≥0∞) * ε₀
        ≤ ∫⁻ x : EuclideanSpace ℝ (Fin d), f x := by
  have hmass : (volume.withDensity f) Set.univ = ∫⁻ x : EuclideanSpace ℝ (Fin d), f x := by
    rw [withDensity_apply f MeasurableSet.univ, Measure.restrict_univ]
  have : IsFiniteMeasure (volume.withDensity f) :=
    ⟨by rw [hmass]; exact lt_top_iff_ne_top.mpr hfin⟩
  refine ⟨bubbleSet_isClosed _ ε₀, bubbleSet_finite _ hε₀, ?_⟩
  rw [← hmass]
  exact bubbleSet_ncard_mul_le _ hε₀

end Frontier

