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
open scoped ENNReal

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

This file formalizes the *bubbling* (energy concentration) part of Uhlenbeck compactness for
Yang–Mills connections, in the measure-theoretic form in which it is used.

A sequence of connections `A n` on a bundle over a Riemannian manifold `X` gives rise to the
sequence of *energy measures* `mu n = |F_{A n}|² dvol`, and a uniform energy bound
`mu n X ≤ E < ∞` is the standing hypothesis of Uhlenbeck's theorem.  The analytic heart of the
theorem (ε-regularity) provides a threshold `eps > 0` below which the connections converge
smoothly, so that failure of compactness is confined to the *bubble set*: those points where
every ball eventually carries at least `eps` of energy.

The results proved here are the quantization/counting half of the statement, which is the part
that is purely about the energy measures:

* `Frontier.uhlenbeck_bubbling` : the bubble set is **finite** and
  `eps * (number of bubbles) ≤ E`;
* `Frontier.uhlenbeck_bubbling_ncard_le` : hence at most `E / eps` bubbles;
* `Frontier.bubbleSet_eq_empty_of_energy_lt` : **base case / removable singularity**, if the
  total energy stays below the ε-regularity threshold, no bubbling occurs at all;
* `Frontier.bubbleSet_const` : for a single limiting energy measure, bubble points are exactly
  the atoms of mass at least `eps` — bubbling is concentration of energy in atoms;
* `Frontier.bubbleSet_const_eq_empty_of_noAtoms` : a non-atomic limiting energy measure has no
  bubbles (removable singularity for the limit);
* `Frontier.uhlenbeck_bubbling_energyDensity` : the same statement phrased directly for
  curvature energy densities `|F_{A n}|²` integrated against the volume measure.
-/

namespace Frontier

open MeasureTheory Filter Metric Set

section Separation

variable {X : Type*} [MetricSpace X]

/-- A finite set of points in a metric space can be surrounded by pairwise disjoint balls
of a common positive radius. -/
lemma exists_radius_pairwiseDisjoint_ball (T : Finset X) :
    ∃ r : ℝ, 0 < r ∧ (↑T : Set X).PairwiseDisjoint (fun x => Metric.ball x r) := by
  classical
  set P : Finset (X × X) := (T ×ˢ T).filter (fun p => p.1 ≠ p.2) with hP
  have hmem : ∀ x y : X, x ∈ T → y ∈ T → x ≠ y → (x, y) ∈ P := by
    intro x y hx hy hxy
    simp [hP, Finset.mem_filter, Finset.mem_product, hx, hy, hxy]
  rcases P.eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, ?_⟩
    intro x hx y hy hxy
    have hmemP := hmem x y hx hy hxy
    rw [hemp] at hmemP
    exact absurd hmemP (Finset.notMem_empty _)
  · obtain ⟨p, hpP, hpmin⟩ := P.exists_min_image (fun p => dist p.1 p.2) hne
    have hp : p.1 ≠ p.2 := by
      have hpP' := hpP
      simp only [hP, Finset.mem_filter] at hpP'
      exact hpP'.2
    have hpos : 0 < dist p.1 p.2 := dist_pos.mpr hp
    refine ⟨dist p.1 p.2 / 2, by linarith, ?_⟩
    intro x hx y hy hxy
    have hxy' := hpmin (x, y) (hmem x y hx hy hxy)
    exact Metric.ball_disjoint_ball (by simpa using by linarith [hxy'])

end Separation

section Bubbles

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- If finitely many balls of radius `r` centred at points of `T` are pairwise disjoint and
each carries at least energy `eps`, then `eps * #T` is at most the total energy. -/
lemma mul_card_le_measure_univ (mu : Measure X) (eps : ℝ≥0∞) (T : Finset X) (r : ℝ)
    (hdisj : (↑T : Set X).PairwiseDisjoint (fun x => Metric.ball x r))
    (h : ∀ x ∈ T, eps ≤ mu (Metric.ball x r)) :
    eps * T.card ≤ mu Set.univ := by
  have hsum : mu (⋃ x ∈ T, Metric.ball x r) = ∑ x ∈ T, mu (Metric.ball x r) :=
    measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)
  calc eps * T.card = ∑ _x ∈ T, eps := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ T, mu (Metric.ball x r) := Finset.sum_le_sum h
    _ = mu (⋃ x ∈ T, Metric.ball x r) := hsum.symm
    _ ≤ mu Set.univ := measure_mono (Set.subset_univ _)

/-- The **bubble set** (concentration set) of a sequence of energy measures `mu n` at
threshold `eps`: the points `x` such that on *every* ball around `x`, the energy is
eventually at least `eps`.

In the Yang–Mills setting, `mu n` is the energy measure `|F_{A n}|² dvol` of a sequence of
connections `A n`, and `bubbleSet mu eps` is the set of points where bubbling occurs, `eps`
being the ε-regularity threshold. -/
def bubbleSet (mu : ℕ → Measure X) (eps : ℝ≥0∞) : Set X :=
  {x : X | ∀ r : ℝ, 0 < r → ∀ᶠ n in atTop, eps ≤ mu n (Metric.ball x r)}

omit [OpensMeasurableSpace X] in
/-- Away from the bubble set, ε-regularity applies: there is a ball on which the energy is
frequently below the threshold. -/
lemma notMem_bubbleSet_iff (mu : ℕ → Measure X) (eps : ℝ≥0∞) (x : X) :
    x ∉ bubbleSet mu eps ↔ ∃ r : ℝ, 0 < r ∧ ∃ᶠ n in atTop, mu n (Metric.ball x r) < eps := by
  simp only [bubbleSet, Set.mem_setOf_eq, not_forall, Filter.not_eventually, not_le,
    exists_prop]

/-- Energy count for a finite family of bubble points: disjoint balls around distinct bubble
points each carry at least `eps` of energy at a common (large) time. -/
lemma mul_card_le_of_subset_bubbleSet {mu : ℕ → Measure X} {E eps : ℝ≥0∞}
    (hbdd : ∀ n, mu n Set.univ ≤ E) (T : Finset X) (hT : (↑T : Set X) ⊆ bubbleSet mu eps) :
    eps * T.card ≤ E := by
  obtain ⟨r, hr, hdisj⟩ := exists_radius_pairwiseDisjoint_ball T
  have hev : ∀ᶠ n in atTop, ∀ x ∈ T, eps ≤ mu n (Metric.ball x r) := by
    refine (Filter.eventually_all_finset T).mpr ?_
    intro x hx
    exact hT (by exact_mod_cast hx) r hr
  obtain ⟨n, hn⟩ := hev.exists
  exact (mul_card_le_measure_univ (mu n) eps T r hdisj hn).trans (hbdd n)

/-- **Uhlenbeck bubbling.**  For a sequence of Yang–Mills fields whose energies `mu n`
(i.e. `|F_{A n}|² dvol`) are uniformly bounded by `E < ∞`, and any positive ε-regularity
threshold `eps`, the set of bubble points is *finite*, and the number of bubbles obeys the
energy quantization bound `eps * (number of bubbles) ≤ E`. -/
theorem uhlenbeck_bubbling {mu : ℕ → Measure X} {E eps : ℝ≥0∞}
    (heps : eps ≠ 0) (hE : E ≠ ⊤) (hbdd : ∀ n, mu n Set.univ ≤ E) :
    (bubbleSet mu eps).Finite ∧ eps * (bubbleSet mu eps).ncard ≤ E := by
  set S : Set X := bubbleSet mu eps with hS
  have key : ∀ T : Finset X, (↑T : Set X) ⊆ S → eps * T.card ≤ E := fun T hT =>
    mul_card_le_of_subset_bubbleSet hbdd T hT
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt (r := E / eps) (ENNReal.div_ne_top hE heps)
  have hEk : E < eps * k := by
    rw [ENNReal.div_lt_iff (Or.inl heps) (Or.inr hE)] at hk
    simpa [mul_comm] using hk
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨t, hts, htc⟩ := Set.Infinite.exists_subset_card_eq hinf k
    have h1 := key t hts
    rw [htc] at h1
    exact absurd h1 (not_le.mpr hEk)
  refine ⟨hfin, ?_⟩
  have h2 := key hfin.toFinset (by simp)
  rwa [Set.ncard_eq_toFinset_card S hfin]

/-- Quantitative form of Uhlenbeck bubbling: there are at most `E / eps` bubbles. -/
theorem uhlenbeck_bubbling_ncard_le {mu : ℕ → Measure X} {E eps : ℝ≥0∞}
    (heps : eps ≠ 0) (hE : E ≠ ⊤) (hbdd : ∀ n, mu n Set.univ ≤ E) :
    ((bubbleSet mu eps).ncard : ℝ≥0∞) ≤ E / eps := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl heps) (Or.inr hE), mul_comm]
  exact (uhlenbeck_bubbling heps hE hbdd).2

/-- **Removable singularity, base case (ε-regularity regime).**  If the total energy stays
below the threshold `eps`, then no bubbling occurs at all. -/
theorem bubbleSet_eq_empty_of_energy_lt {mu : ℕ → Measure X} {E eps : ℝ≥0∞}
    (hlt : E < eps) (hbdd : ∀ n, mu n Set.univ ≤ E) :
    bubbleSet mu eps = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro x hx
  have h1 : eps * ({x} : Finset X).card ≤ E := by
    refine mul_card_le_of_subset_bubbleSet hbdd {x} ?_
    intro y hy
    have : y = x := by simpa using hy
    exact this ▸ hx
  simp only [Finset.card_singleton, Nat.cast_one, mul_one] at h1
  exact absurd h1 (not_le.mpr hlt)

end Bubbles

section SingleMeasure

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- If every ball around `x` has measure at least `eps`, then the singleton `{x}` does, for a
finite measure: the energy really concentrates in an atom. -/
lemma le_measure_singleton_of_forall_ball (mu : Measure X) [IsFiniteMeasure mu] (eps : ℝ≥0∞)
    (x : X) (h : ∀ r : ℝ, 0 < r → eps ≤ mu (Metric.ball x r)) : eps ≤ mu {x} := by
  have hint : (⋂ n : ℕ, Metric.ball x (1 / (n + 1) : ℝ)) = {x} := by
    ext y
    simp only [Set.mem_iInter, Metric.mem_ball, Set.mem_singleton_iff]
    constructor
    · intro hy
      by_contra hne
      have hpos : 0 < dist y x := dist_pos.mpr hne
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      exact absurd (hy n) (not_lt.mpr (le_of_lt hn))
    · rintro rfl
      intro n
      have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simpa using hn
  have hanti : Antitone (fun n : ℕ => Metric.ball x (1 / (n + 1) : ℝ)) := by
    intro m n hmn
    refine Metric.ball_subset_ball (one_div_le_one_div_of_le (by positivity) ?_)
    exact_mod_cast Nat.succ_le_succ hmn
  have htend := MeasureTheory.tendsto_measure_iInter_atTop (μ := mu)
    (s := fun n : ℕ => Metric.ball x (1 / (n + 1) : ℝ))
    (fun _ => measurableSet_ball.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hint] at htend
  refine ge_of_tendsto htend ?_
  filter_upwards with n
  exact h _ (by positivity)

/-- For a single finite energy measure, the bubble points are exactly the atoms of mass at
least `eps`: concentration of energy at a point *is* an atom of the energy measure. -/
theorem bubbleSet_const (mu : Measure X) [IsFiniteMeasure mu] (eps : ℝ≥0∞) :
    bubbleSet (fun _ => mu) eps = {x : X | eps ≤ mu {x}} := by
  ext x
  simp only [bubbleSet, Set.mem_setOf_eq]
  constructor
  · intro h
    refine le_measure_singleton_of_forall_ball mu eps x ?_
    intro r hr
    obtain ⟨_, hn⟩ := (h r hr).exists
    exact hn
  · intro h r hr
    filter_upwards with n
    exact h.trans (measure_mono (Set.singleton_subset_iff.mpr (Metric.mem_ball_self hr)))

/-- **No bubbling for a non-atomic energy measure**: if the limiting energy measure has no
atoms then the bubble set is empty, i.e. the singularity is removable. -/
theorem bubbleSet_const_eq_empty_of_noAtoms (mu : Measure X) [IsFiniteMeasure mu]
    [NoAtoms mu] {eps : ℝ≥0∞} (heps : eps ≠ 0) :
    bubbleSet (fun _ => mu) eps = ∅ := by
  rw [bubbleSet_const]
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro x hx
  simp only [Set.mem_setOf_eq, measure_singleton, nonpos_iff_eq_zero] at hx
  exact heps hx

end SingleMeasure

section YangMillsEnergy

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Bubbling stated directly for energy densities: `F n` plays the role of the pointwise
curvature energy `|F_{A n}|²` of a sequence of connections, integrated against the volume
measure `vol`.  If the total energies are bounded by `E < ∞`, only finitely many bubble
points can occur, and their number is at most `E / eps`. -/
theorem uhlenbeck_bubbling_energyDensity (vol : Measure X) (F : ℕ → X → ℝ≥0∞) {E eps : ℝ≥0∞} (heps : eps ≠ 0) (hE : E ≠ ⊤)
    (hbdd : ∀ n, ∫⁻ x, F n x ∂vol ≤ E) :
    let S : Set X := {x : X | ∀ r : ℝ, 0 < r →
      ∀ᶠ n in atTop, eps ≤ ∫⁻ y in Metric.ball x r, F n y ∂vol}
    S.Finite ∧ eps * S.ncard ≤ E ∧ (S.ncard : ℝ≥0∞) ≤ E / eps := by
  intro S
  set mu : ℕ → Measure X := fun n => vol.withDensity (F n) with hmu
  have hball : ∀ (n : ℕ) (x : X) (r : ℝ),
      mu n (Metric.ball x r) = ∫⁻ y in Metric.ball x r, F n y ∂vol := by
    intro n x r
    rw [hmu, withDensity_apply _ measurableSet_ball]
  have hSeq : S = bubbleSet mu eps := by
    ext x
    simp only [S, bubbleSet, Set.mem_setOf_eq, hball]
  have hbdd' : ∀ n, mu n Set.univ ≤ E := by
    intro n
    rw [hmu, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hbdd n
  rw [hSeq]
  exact ⟨(uhlenbeck_bubbling heps hE hbdd').1, (uhlenbeck_bubbling heps hE hbdd').2,
    uhlenbeck_bubbling_ncard_le heps hE hbdd'⟩

end YangMillsEnergy

end Frontier

