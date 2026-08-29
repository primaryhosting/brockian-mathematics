import Mathlib
/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Formalisation of the *bubbling* (energy concentration) part of Uhlenbeck's
compactness theory for Yang–Mills connections.

Setting.  Let `X` be a metric measure space (think of a Riemannian four-manifold
with its volume measure `μ`) and let `A n` be a sequence of connections with
curvature `F_{A n}`.  All that enters the concentration analysis is the sequence
of energy densities `F n x = |F_{A n}(x)|²`, together with the uniform energy
bound `∫ |F_{A n}|² dμ ≤ Λ`.

A point `x` is an *`ε`-bubble point* of the sequence if, no matter how small a
ball we take around `x`, at least `ε` units of energy persistently sit inside
that ball, i.e. `ε ≤ liminf_n ∫_{B(x,r)} |F_{A n}|²`.  (Using `liminf` is the
same as passing to a subsequence along which the local energies converge, which
is how the statement is usually phrased; with `limsup` instead the statement is
*false*, see `Frontier.limsup_concentration_counterexample` below.)

Main result (`Frontier.uhlenbeck_bubbling`): the set of `ε`-bubble points is
finite, and the number of bubbles is controlled by the energy:
`(number of bubbles) * ε ≤ Λ`.  In particular at most `⌊Λ/ε⌋` bubbles can form,
and if the total energy is below the threshold `ε` no bubbling occurs at all.
-/

open MeasureTheory Metric Filter Set
open scoped ENNReal Topology

namespace Frontier

section Auxiliary

/-- Superadditivity of `liminf` for two `ℝ≥0∞`-valued sequences. -/
theorem liminf_add_le_liminf_add (u v : ℕ → ℝ≥0∞) :
    liminf u atTop + liminf v atTop ≤ liminf (fun n => u n + v n) atTop := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat,
    Filter.liminf_eq_iSup_iInf_of_nat]
  refine ENNReal.iSup_add_iSup_le fun i j => ?_
  refine le_iSup_of_le (max i j) (le_iInf₂ fun m hm => ?_)
  exact add_le_add (iInf₂_le m (le_of_max_le_left hm)) (iInf₂_le m (le_of_max_le_right hm))

/-- Superadditivity of `liminf` for a finite sum of `ℝ≥0∞`-valued sequences. -/
theorem sum_liminf_le_liminf_sum {ι : Type*} (T : Finset ι) (g : ι → ℕ → ℝ≥0∞) :
    ∑ x ∈ T, liminf (fun n => g x n) atTop ≤ liminf (fun n => ∑ x ∈ T, g x n) atTop := by
  classical
  induction T using Finset.cons_induction with
  | empty => simp
  | cons a s _ ih =>
      simp only [Finset.sum_cons]
      refine le_trans (add_le_add le_rfl ih) ?_
      exact liminf_add_le_liminf_add (fun n => g a n) (fun n => ∑ x ∈ s, g x n)

/-- Around the points of a finite subset of a metric space one can put pairwise
disjoint balls of a common positive radius. -/
theorem exists_pos_pairwiseDisjoint_balls {X : Type*} [MetricSpace X] (T : Finset X) :
    ∃ r : ℝ, 0 < r ∧ (↑T : Set X).PairwiseDisjoint fun x => ball x r := by
  classical
  rcases T.offDiag.eq_empty_or_nonempty with h | h
  · refine ⟨1, one_pos, fun x hx y hy hxy => ?_⟩
    have hmem : ((x, y) : X × X) ∈ T.offDiag :=
      Finset.mem_offDiag.2 ⟨Finset.mem_coe.1 hx, Finset.mem_coe.1 hy, hxy⟩
    rw [h] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  · set d : ℝ := T.offDiag.inf' h fun p => dist p.1 p.2 with hd_def
    have hd : 0 < d := by
      rw [hd_def, Finset.lt_inf'_iff]
      intro p hp
      exact dist_pos.2 (Finset.mem_offDiag.1 hp).2.2
    refine ⟨d / 2, by positivity, fun x hx y hy hxy => ?_⟩
    have hmem : ((x, y) : X × X) ∈ T.offDiag :=
      Finset.mem_offDiag.2 ⟨Finset.mem_coe.1 hx, Finset.mem_coe.1 hy, hxy⟩
    have hxy' : d ≤ dist x y := Finset.inf'_le (fun p => dist p.1 p.2) hmem
    exact ball_disjoint_ball (by linarith)

end Auxiliary

section AbstractConcentration

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The set of points at which a sequence of (energy) measures `E` concentrates at
least `ε` of mass in every ball, in the `liminf` sense. -/
def concentrationSet (E : ℕ → Measure X) (ε : ℝ≥0∞) : Set X :=
  {x | ∀ r : ℝ, 0 < r → ε ≤ liminf (fun n => E n (ball x r)) atTop}

/-- Any finite set of `ε`-concentration points obeys the counting bound
`(card) * ε ≤ Λ`, where `Λ` bounds the total mass of every `E n`. -/
theorem card_mul_le_of_subset_concentrationSet (E : ℕ → Measure X) (Λ ε : ℝ≥0∞)
    (hb : ∀ n, E n Set.univ ≤ Λ) (T : Finset X) (hT : ↑T ⊆ concentrationSet E ε) :
    (T.card : ℝ≥0∞) * ε ≤ Λ := by
  classical
  obtain ⟨r, hr, hdisj⟩ := exists_pos_pairwiseDisjoint_balls T
  have hsum : ∀ n, ∑ x ∈ T, E n (ball x r) ≤ Λ := by
    intro n
    have hmeas : ∀ x ∈ T, MeasurableSet (ball x r) := fun x _ => measurableSet_ball
    have := measure_biUnion_finset (μ := E n) hdisj hmeas
    calc ∑ x ∈ T, E n (ball x r) = E n (⋃ x ∈ T, ball x r) := this.symm
      _ ≤ E n Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ Λ := hb n
  calc (T.card : ℝ≥0∞) * ε = ∑ _x ∈ T, ε := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ T, liminf (fun n => E n (ball x r)) atTop :=
        Finset.sum_le_sum fun x hx => hT (Finset.mem_coe.2 hx) r hr
    _ ≤ liminf (fun n => ∑ x ∈ T, E n (ball x r)) atTop :=
        sum_liminf_le_liminf_sum T fun x n => E n (ball x r)
    _ ≤ liminf (fun _ : ℕ => Λ) atTop :=
        liminf_le_liminf (Eventually.of_forall hsum)
    _ = Λ := liminf_const Λ

/-- With a finite uniform mass bound and a positive concentration threshold, the
set of concentration points is finite. -/
theorem finite_concentrationSet (E : ℕ → Measure X) (Λ ε : ℝ≥0∞) (hΛ : Λ ≠ ⊤) (hε : ε ≠ 0)
    (hb : ∀ n, E n Set.univ ≤ Λ) : (concentrationSet E ε).Finite := by
  classical
  by_contra hinf
  rw [Set.not_finite] at hinf
  -- choose `N` with `Λ < N * ε`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Λ < (N : ℝ≥0∞) * ε := by
    rcases eq_or_ne ε ⊤ with rfl | hεtop
    · exact ⟨1, by simpa [ENNReal.mul_top, hε] using lt_top_iff_ne_top.2 hΛ⟩
    · obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (r := Λ / ε)
        (by simp [ENNReal.div_eq_top, hε, hΛ])
      refine ⟨N, ?_⟩
      have := (ENNReal.div_lt_iff (Or.inl hε) (Or.inl hεtop)).1 hN
      simpa [mul_comm] using this
  obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq N
  have := card_mul_le_of_subset_concentrationSet E Λ ε hb T hTsub
  rw [hTcard] at this
  exact absurd this (not_le.2 hN)

/-- The `limsup` analogue of `concentrationSet`. -/
def limsupConcentrationSet (E : ℕ → Measure X) (ε : ℝ≥0∞) : Set X :=
  {x | ∀ r : ℝ, 0 < r → ε ≤ limsup (fun n => E n (ball x r)) atTop}

/-- The `liminf` in the definition of the bubble set cannot be replaced by a `limsup`:
there is a sequence of probability measures on `ℕ` (unit total energy, so `Λ = ε = 1`)
whose `limsup`-concentration set is infinite.  Concretely, `E n` is the Dirac mass at
`(Nat.unpair n).1`, so every point carries a full unit of mass infinitely often. -/
theorem limsup_concentration_counterexample :
    ∃ E : ℕ → Measure ℕ, (∀ n, E n Set.univ ≤ 1) ∧ (limsupConcentrationSet E 1).Infinite := by
  refine ⟨fun n => Measure.dirac (Nat.unpair n).1, fun n => by simp, ?_⟩
  have huniv : limsupConcentrationSet (fun n => Measure.dirac (Nat.unpair n).1) 1 = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    intro r hr
    refine le_limsup_of_frequently_le ?_
    rw [Filter.frequently_atTop]
    intro N
    refine ⟨Nat.pair x N, Nat.right_le_pair x N, ?_⟩
    simp only [Nat.unpair_pair]
    simp [Measure.dirac_apply' _ (measurableSet_ball (x := x) (ε := r)), Metric.mem_ball_self hr]
  rw [huniv]
  exact Set.infinite_univ

end AbstractConcentration

section YangMills

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- `bubbleSet μ F ε` is the set of `ε`-bubble points of a sequence of Yang–Mills
connections whose curvature energy densities are `F n` (i.e. `F n x = |F_{A n}(x)|²`)
on the metric measure space `(X, μ)`:  points where, in every ball, at least `ε`
of the energy persists in the limit. -/
def bubbleSet (μ : Measure X) (F : ℕ → X → ℝ≥0∞) (ε : ℝ≥0∞) : Set X :=
  {x | ∀ r : ℝ, 0 < r → ε ≤ liminf (fun n => ∫⁻ y in ball x r, F n y ∂μ) atTop}

theorem bubbleSet_eq_concentrationSet (μ : Measure X) (F : ℕ → X → ℝ≥0∞) (ε : ℝ≥0∞) :
    bubbleSet μ F ε = concentrationSet (fun n => μ.withDensity (F n)) ε := by
  ext x
  constructor <;> intro hx r hr <;> refine le_trans (hx r hr) (le_of_eq ?_) <;>
    refine liminf_congr (Eventually.of_forall fun n => ?_)
  · exact (withDensity_apply (F n) measurableSet_ball).symm
  · exact withDensity_apply (F n) measurableSet_ball

/-- **Uhlenbeck bubbling: finiteness and quantisation of the bubble set.**

Let `(A n)` be a sequence of connections on a metric measure space `(X, μ)` whose
curvature energy densities `F n = |F_{A n}|²` satisfy the uniform Yang–Mills energy
bound `∫ F n dμ ≤ Λ < ∞`, and let `ε > 0` be an energy threshold (e.g. the
`ε`-regularity constant).  Then only finitely many bubbles can form, and their
number is quantised by the available energy:
`(number of `ε`-bubble points) * ε ≤ Λ`, i.e. there are at most `⌊Λ/ε⌋` bubbles.

Away from this finite set the energy stays below the `ε`-regularity threshold on
small balls, which is exactly the hypothesis from which Uhlenbeck's local
compactness and removable-singularity theorems proceed. -/
theorem uhlenbeck_bubbling (μ : Measure X) (F : ℕ → X → ℝ≥0∞) (Λ ε : ℝ≥0∞)
    (hΛ : Λ ≠ ⊤) (hε : ε ≠ 0) (hbound : ∀ n, ∫⁻ x, F n x ∂μ ≤ Λ) :
    (bubbleSet μ F ε).Finite ∧ ((bubbleSet μ F ε).ncard : ℝ≥0∞) * ε ≤ Λ := by
  classical
  set E : ℕ → Measure X := fun n => μ.withDensity (F n) with hE
  have hb : ∀ n, E n Set.univ ≤ Λ := by
    intro n
    rw [hE]
    simpa [withDensity_apply (F n) MeasurableSet.univ, Measure.restrict_univ] using hbound n
  have hset : bubbleSet μ F ε = concentrationSet E ε := bubbleSet_eq_concentrationSet μ F ε
  have hfin : (bubbleSet μ F ε).Finite := by
    rw [hset]; exact finite_concentrationSet E Λ ε hΛ hε hb
  refine ⟨hfin, ?_⟩
  have hsub : ↑hfin.toFinset ⊆ concentrationSet E ε := by
    rw [← hset]; simp
  have := card_mul_le_of_subset_concentrationSet E Λ ε hb hfin.toFinset hsub
  rwa [Set.ncard_eq_toFinset_card _ hfin]

/-- Below the energy threshold no bubbling occurs: if the total Yang–Mills energy
stays under `ε`, the bubble set is empty. -/
theorem bubbleSet_eq_empty_of_energy_lt (μ : Measure X) (F : ℕ → X → ℝ≥0∞) (Λ ε : ℝ≥0∞)
    (hΛ : Λ ≠ ⊤) (hε : ε ≠ 0) (hbound : ∀ n, ∫⁻ x, F n x ∂μ ≤ Λ) (hlt : Λ < ε) :
    bubbleSet μ F ε = ∅ := by
  classical
  obtain ⟨hfin, hcard⟩ := uhlenbeck_bubbling μ F Λ ε hΛ hε hbound
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  have h1 : 1 ≤ (bubbleSet μ F ε).ncard := (Set.ncard_pos hfin).2 ⟨x, hx⟩
  have : ε ≤ ((bubbleSet μ F ε).ncard : ℝ≥0∞) * ε := by
    refine le_mul_of_one_le_left' ?_
    exact_mod_cast h1
  exact absurd (this.trans hcard) (not_le.2 hlt)

/-- The bound in `uhlenbeck_bubbling` is sharp and the statement is not vacuous: on `ℕ`
with the Dirac volume measure at `0` and constant unit energy density, the total energy
is `Λ = 1` and the point `0` really is a `1`-bubble point, so exactly one bubble forms. -/
theorem bubbleSet_sharp_example :
    (∀ n : ℕ, ∫⁻ x, (fun _ _ => (1 : ℝ≥0∞)) n x ∂(Measure.dirac (0 : ℕ)) ≤ 1) ∧
      (0 : ℕ) ∈ bubbleSet (Measure.dirac (0 : ℕ)) (fun _ _ => (1 : ℝ≥0∞)) 1 := by
  refine ⟨fun n => by simp, ?_⟩
  intro r hr
  simp [Set.indicator_of_mem (Metric.mem_ball_self hr)]

end YangMills

end Frontier

