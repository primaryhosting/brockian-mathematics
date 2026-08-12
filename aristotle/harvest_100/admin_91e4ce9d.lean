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

open MeasureTheory Metric Set Filter Function
open scoped ENNReal Topology

/-! ## The Yang–Mills energy

A Yang–Mills field on a manifold `X` is modelled here by its curvature `F : X → V`, a field with
values in a normed space `V` (in the geometric situation, `V` is the space of `𝔤`-valued
two-forms).  Its Yang–Mills energy over a region `s` is `∫_s ‖F‖²`. -/

section Energy

variable {X : Type*} [MeasurableSpace X] {V : Type*} [NormedAddCommGroup V]

/-- The Yang–Mills energy `∫_s ‖F‖²` of a curvature field `F` over the region `s`. -/
noncomputable def energyOn (mu : Measure X) (F : X → V) (s : Set X) : ℝ≥0∞ :=
  ∫⁻ x in s, (‖F x‖₊ : ℝ≥0∞) ^ 2 ∂mu

lemma energyOn_mono (mu : Measure X) (F : X → V) {s t : Set X} (h : s ⊆ t) :
    energyOn mu F s ≤ energyOn mu F t :=
  lintegral_mono_set h

lemma energyOn_biUnion_finset {mu : Measure X} {F : X → V} {ι : Type*} {S : Finset ι}
    {t : ι → Set X} (hd : Set.PairwiseDisjoint (↑S) t) (hm : ∀ b ∈ S, MeasurableSet (t b)) :
    energyOn mu F (⋃ b ∈ S, t b) = ∑ b ∈ S, energyOn mu F (t b) :=
  lintegral_biUnion_finset hd hm _

end Energy

/-! ## Bubbling: the concentration set of a sequence of Yang–Mills fields -/

section Bubble

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {V : Type*} [NormedAddCommGroup V]

/-- The *bubbling set* (concentration set) at threshold `eps` of a sequence `F` of curvature
fields: the points `x` such that, on *every* ball around `x`, the energy of `F n` is eventually
at least `eps`.  These are exactly the points where energy can concentrate ("bubble off") in the
limit. -/
def bubbleSet (mu : Measure X) (F : ℕ → X → V) (eps : ℝ≥0∞) : Set X :=
  {x : X | ∀ r : ℝ, 0 < r → ∀ᶠ n in atTop, eps ≤ energyOn mu (F n) (ball x r)}

omit [OpensMeasurableSpace X] in
lemma bubbleSet_mono {mu : Measure X} {F : ℕ → X → V} {eps eps' : ℝ≥0∞} (h : eps' ≤ eps) :
    bubbleSet mu F eps ⊆ bubbleSet mu F eps' := by
  intro x hx r hr
  exact (hx r hr).mono fun _ hn => le_trans h hn

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- A finite set in a metric space has a positive separation constant. -/
lemma exists_pos_separation (S : Finset X) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ dist x y := by
  classical
  have hpair : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      dist x y ∈ S.offDiag.image (fun p : X × X => dist p.1 p.2) := by
    intro x hx y hy hxy
    have hmem : ((x, y) : X × X) ∈ S.offDiag := Finset.mem_offDiag.2 ⟨hx, hy, hxy⟩
    exact Finset.mem_image_of_mem (fun p : X × X => dist p.1 p.2) hmem
  by_cases hT : (S.offDiag.image (fun p : X × X => dist p.1 p.2)).Nonempty
  · refine ⟨(S.offDiag.image (fun p : X × X => dist p.1 p.2)).min' hT, ?_, fun x hx y hy hxy => ?_⟩
    · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 (Finset.min'_mem _ hT)
      obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.1 hp
      rw [← hpe]
      exact dist_pos.2 hne
    · exact Finset.min'_le _ _ (hpair x hx y hy hxy)
  · refine ⟨1, one_pos, fun x hx y hy hxy => ?_⟩
    exact absurd (hpair x hx y hy hxy) (fun hmem => hT ⟨_, hmem⟩)

/-- **Energy quantization bound.**  Any finite family of bubbling points consumes at least
`eps` of energy each, hence has at most `Etot / eps` elements. -/
lemma finset_card_mul_le_of_subset_bubbleSet {mu : Measure X} {F : ℕ → X → V} {eps Etot : ℝ≥0∞}
    (hbdd : ∀ n, energyOn mu (F n) Set.univ ≤ Etot)
    (S : Finset X) (hS : ↑S ⊆ bubbleSet mu F eps) :
    (S.card : ℝ≥0∞) * eps ≤ Etot := by
  classical
  obtain ⟨d, hd, hsep⟩ := exists_pos_separation S
  have key : ∀ᶠ n in atTop, ∀ x ∈ S, eps ≤ energyOn mu (F n) (ball x (d / 2)) := by
    rw [Filter.eventually_all_finset]
    intro x hx
    exact hS hx (d / 2) (by positivity)
  obtain ⟨n, hn⟩ := key.exists
  have hdisj : (↑S : Set X).PairwiseDisjoint (fun x => ball x (d / 2)) := by
    intro x hx y hy hxy
    refine Metric.ball_disjoint_ball ?_
    have := hsep x (by exact_mod_cast hx) y (by exact_mod_cast hy) hxy
    linarith
  calc (S.card : ℝ≥0∞) * eps = ∑ _x ∈ S, eps := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ S, energyOn mu (F n) (ball x (d / 2)) := Finset.sum_le_sum hn
    _ = energyOn mu (F n) (⋃ x ∈ S, ball x (d / 2)) :=
        (energyOn_biUnion_finset hdisj (fun b _ => measurableSet_ball)).symm
    _ ≤ energyOn mu (F n) Set.univ := energyOn_mono _ _ (subset_univ _)
    _ ≤ Etot := hbdd n

/-- **Finiteness of the bubbling set.**  A sequence of Yang–Mills fields of uniformly bounded
energy can concentrate at only finitely many points. -/
theorem bubbleSet_finite {mu : Measure X} {F : ℕ → X → V} {eps Etot : ℝ≥0∞}
    (hEtot : Etot ≠ ∞) (heps : eps ≠ 0)
    (hbdd : ∀ n, energyOn mu (F n) Set.univ ≤ Etot) :
    (bubbleSet mu F eps).Finite := by
  classical
  set e : ℝ≥0∞ := min eps 1 with he
  have he0 : e ≠ 0 := by
    have : (0 : ℝ≥0∞) < e := lt_min (pos_iff_ne_zero.2 heps) one_pos
    exact this.ne'
  have hetop : e ≠ ∞ := ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Etot / e < (N : ℝ≥0∞) :=
    ENNReal.exists_nat_gt (ENNReal.div_ne_top hEtot he0)
  have hNe : Etot < (N : ℝ≥0∞) * e :=
    (ENNReal.div_lt_iff (Or.inl he0) (Or.inl hetop)).1 hN
  have hsub : (bubbleSet mu F eps) ⊆ bubbleSet mu F e :=
    bubbleSet_mono (min_le_left _ _)
  obtain ⟨S, hSsub, hScard⟩ := (hinf.mono hsub).exists_subset_card_eq N
  have hcard := finset_card_mul_le_of_subset_bubbleSet hbdd S hSsub
  rw [hScard] at hcard
  exact absurd hcard (not_le.2 hNe)

end Bubble

/-! ## The main theorem -/

/-- Four-dimensional Euclidean space, the base manifold of the model Yang–Mills problem. -/
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

/-- **Uhlenbeck bubbling.**

Let `F n` be a sequence of Yang–Mills curvature fields on `ℝ⁴` with uniformly bounded
Yang–Mills energy `Etot < ∞`, and let `eps > 0` be an energy threshold (in the geometric theory,
the `ε`-regularity threshold).  Then:

* the bubbling set — the set of points at which the energy persistently concentrates at scale
  `eps` on all small balls — is **finite**;
* it satisfies the **quantization bound** `#{bubbles} · eps ≤ Etot`, so at most `Etot / eps`
  bubbles can form;
* away from the bubbling set, the fields are **frequently subcritical** on some fixed ball, i.e.
  the hypothesis of `ε`-regularity is available there along a subsequence.

This is the combinatorial core of Uhlenbeck's compactness theorem: modulo `ε`-regularity, the
only obstruction to compactness is the loss of at most `Etot / eps` quanta of energy at finitely
many points. -/
theorem uhlenbeck_bubbling {V : Type*} [NormedAddCommGroup V]
    (F : ℕ → E4 → V) (Etot eps : ℝ≥0∞) (hEtot : Etot ≠ ∞) (heps : eps ≠ 0)
    (hbdd : ∀ n, energyOn volume (F n) Set.univ ≤ Etot) :
    (bubbleSet volume F eps).Finite ∧
      ((bubbleSet volume F eps).ncard : ℝ≥0∞) * eps ≤ Etot ∧
      ∀ x ∉ bubbleSet volume F eps, ∃ r : ℝ, 0 < r ∧
        ∃ᶠ n in atTop, energyOn volume (F n) (ball x r) < eps := by
  classical
  have hfin : (bubbleSet volume F eps).Finite := bubbleSet_finite hEtot heps hbdd
  refine ⟨hfin, ?_, ?_⟩
  · have hsub : (↑hfin.toFinset : Set E4) ⊆ bubbleSet volume F eps := by
      simp [Set.Finite.coe_toFinset]
    have hcard := finset_card_mul_le_of_subset_bubbleSet hbdd hfin.toFinset hsub
    rwa [← Set.ncard_eq_toFinset_card _ hfin] at hcard
  · intro x hx
    have hx' : ¬ ∀ r : ℝ, 0 < r → ∀ᶠ n in atTop, eps ≤ energyOn volume (F n) (ball x r) := hx
    rw [not_forall] at hx'
    obtain ⟨r, hr⟩ := hx'
    rw [Classical.not_imp] at hr
    exact ⟨r, hr.1, by simpa only [Filter.not_eventually, not_le] using hr.2⟩

/-- If the total energy stays below the threshold `eps`, no bubbling occurs at all. -/
theorem bubbleSet_eq_empty_of_energy_lt {V : Type*} [NormedAddCommGroup V]
    (F : ℕ → E4 → V) (eps : ℝ≥0∞)
    (hbdd : ∀ n, energyOn volume (F n) Set.univ < eps) :
    bubbleSet volume F eps = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have h1 : ∀ᶠ n in atTop, eps ≤ energyOn volume (F n) (ball x 1) := hx 1 one_pos
  have h2 : ∀ᶠ n in atTop, energyOn volume (F n) (ball x 1) < eps := by
    filter_upwards with n using lt_of_le_of_lt (energyOn_mono _ _ (subset_univ _)) (hbdd n)
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  exact absurd hn1 (not_le.2 hn2)

/-! ## Conformal invariance of the four-dimensional Yang–Mills energy

The reason bubbles form in dimension four is that the Yang–Mills energy is *conformally
invariant*: rescaling a connection by `λ` leaves its energy unchanged, so energy can be
concentrated into arbitrarily small balls at no cost. -/

section Rescaling

/-- The curvature of the rescaled connection `A_λ(x) = λ · A(λ x)` is `λ² F(λ x)`. -/
noncomputable def rescale {W V : Type*} [SMul ℝ W] [SMul ℝ V] (lam : ℝ) (F : W → V) : W → V :=
  fun x => (lam ^ 2) • F (lam • x)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

/-- Change of variables under a dilation, for lower Lebesgue integrals over a set. -/
lemma setLIntegral_comp_smul (mu : Measure E) [mu.IsAddHaarMeasure] (g : E → ℝ≥0∞)
    {lam : ℝ} (hlam : lam ≠ 0) {s : Set E} (hs : MeasurableSet s) :
    ∫⁻ x in s, g (lam • x) ∂mu
      = ENNReal.ofReal |(lam ^ (Module.finrank ℝ E))⁻¹| * ∫⁻ y in lam • s, g y ∂mu := by
  have hsmul : MeasurableSet (lam • s) := by
    rw [← Set.image_smul]
    exact ((Homeomorph.smulOfNeZero lam hlam).toMeasurableEquiv.measurableEmbedding).measurableSet_image'
      hs
  have hmapeq : Measure.map (fun x : E => lam • x) mu
      = ENNReal.ofReal |(lam ^ (Module.finrank ℝ E))⁻¹| • mu := Measure.map_addHaar_smul mu hlam
  have h1 : ∫⁻ y, (lam • s).indicator g y ∂(Measure.map (fun x : E => lam • x) mu)
      = ∫⁻ x, (lam • s).indicator g (lam • x) ∂mu :=
    lintegral_map_equiv _ (Homeomorph.smulOfNeZero lam hlam).toMeasurableEquiv
  have h2 : ∀ x : E, (lam • s).indicator g (lam • x) = s.indicator (fun x => g (lam • x)) x := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem ((Set.smul_mem_smul_set_iff₀ hlam _ _).2 hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
      intro hmem
      exact hx ((Set.smul_mem_smul_set_iff₀ hlam _ _).1 hmem)
  simp only [h2] at h1
  rw [hmapeq] at h1
  rw [lintegral_smul_measure, lintegral_indicator hsmul, lintegral_indicator hs] at h1
  exact h1.symm

/-- **Conformal invariance of the Yang–Mills energy in dimension four.**  Rescaling a Yang–Mills
field by a factor `lam > 0` transports its energy from a region `s` to the rescaled region,
without changing its value.  In particular the energy of the rescaled field on the ball of radius
`r/lam` equals the energy of the original field on the ball of radius `r`: energy can be
concentrated at arbitrarily small scales, which is exactly the mechanism of bubbling. -/
theorem energyOn_rescale {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : E4 → V)
    {lam : ℝ} (hlam : 0 < lam) {s : Set E4} (hs : MeasurableSet s) :
    energyOn volume (rescale lam F) s = energyOn volume F (lam • s) := by
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  have hrank : Module.finrank ℝ E4 = 4 := by
    simp [E4]
  have hnorm : ∀ x : E4, ((‖rescale lam F x‖₊ : ℝ≥0∞) ^ 2)
      = ENNReal.ofReal (lam ^ 4) * ((‖F (lam • x)‖₊ : ℝ≥0∞) ^ 2) := by
    intro x
    have h1 : ‖rescale lam F x‖₊ = ‖(lam ^ 2 : ℝ)‖₊ * ‖F (lam • x)‖₊ := by
      simp only [rescale, nnnorm_smul]
    rw [h1]
    push_cast
    rw [mul_pow]
    congr 1
    have h2 : ((‖(lam ^ 2 : ℝ)‖₊ : ℝ≥0∞)) = ENNReal.ofReal (lam ^ 2) := by
      simp [ENNReal.ofReal, Real.nnnorm_of_nonneg (by positivity : (0:ℝ) ≤ lam ^ 2),
        Real.toNNReal_of_nonneg (by positivity : (0:ℝ) ≤ lam ^ 2)]
    rw [h2, ← ENNReal.ofReal_pow (by positivity)]
    ring_nf
  unfold energyOn
  simp only [hnorm]
  rw [lintegral_const_mul' _ _ (by simp),
    setLIntegral_comp_smul volume (fun y => ((‖F y‖₊ : ℝ≥0∞)) ^ 2) hlam0 hs, hrank,
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (lam ^ 4)⁻¹), mul_inv_cancel₀ (by positivity)]
  simp

/-- **Bubbles do occur.**  The statement of `uhlenbeck_bubbling` is not vacuous: given any
Yang–Mills field `G` on `ℝ⁴` carrying at least `eps` of energy on some ball around the origin,
the conformally rescaled sequence `F n = rescale (n+1) G` has the origin in its bubbling set,
while every member of the sequence has exactly the same total energy as `G`.  This is the
standard bubbling construction. -/
theorem zero_mem_bubbleSet_rescale {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : E4 → V) (eps : ℝ≥0∞) {R : ℝ} (hG : eps ≤ energyOn volume G (ball 0 R)) :
    (0 : E4) ∈ bubbleSet volume (fun n : ℕ => rescale ((n : ℝ) + 1) G) eps ∧
      ∀ n : ℕ, energyOn volume (rescale ((n : ℝ) + 1) G) Set.univ
        = energyOn volume G Set.univ := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  constructor
  · intro r hr
    obtain ⟨N, hN⟩ := exists_nat_gt (R / r)
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hball : ((n : ℝ) + 1) • (ball (0 : E4) r) = ball 0 (((n : ℝ) + 1) * r) := by
      rw [smul_ball (ne_of_gt (hpos n)) (0 : E4) r]
      simp [Real.norm_eq_abs, abs_of_nonneg (hpos n).le]
    have hRle : R ≤ ((n : ℝ) + 1) * r := by
      have hNr : R / r < (N : ℝ) := hN
      have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have : R / r < (n : ℝ) + 1 := by linarith
      calc R = R / r * r := by field_simp
        _ ≤ ((n : ℝ) + 1) * r := by nlinarith
    calc eps ≤ energyOn volume G (ball 0 R) := hG
      _ ≤ energyOn volume G (ball 0 (((n : ℝ) + 1) * r)) :=
          energyOn_mono _ _ (Metric.ball_subset_ball hRle)
      _ = energyOn volume (rescale ((n : ℝ) + 1) G) (ball 0 r) := by
          rw [energyOn_rescale G (hpos n) measurableSet_ball, hball]
  · intro n
    rw [energyOn_rescale G (hpos n) MeasurableSet.univ,
      smul_set_univ₀ (ne_of_gt (hpos n))]

end Rescaling

/-! ## Removable singularities -/

/-- **Removable singularity for the energy.**  A puncture carries no Yang–Mills energy: the energy
of a field on a punctured region equals its energy on the whole region.  This is the measure
theoretic half of the removable singularity theorem, and shows that the finite-energy condition
on `s \ {c}` is the same as on `s`. -/
theorem energyOn_diff_singleton {V : Type*} [NormedAddCommGroup V] (F : E4 → V) (s : Set E4)
    (c : E4) : energyOn volume F (s \ {c}) = energyOn volume F s := by
  have hnull : (volume : Measure E4) {c} = 0 := measure_singleton c
  have hae : (s \ {c} : Set E4) =ᵐ[(volume : Measure E4)] s := diff_null_ae_eq_self hnull
  unfold energyOn
  exact setLIntegral_congr hae

/-- **Removable singularity, abelian base case.**  For an abelian (`U(1)`) Yang–Mills field on a
disc, the field equation says that the connection form is (anti)holomorphic; Riemann's removable
singularity theorem then shows that a field which is holomorphic on the punctured disc and
bounded near the puncture extends holomorphically across it.  This is the base case of the
Uhlenbeck removable singularity theorem. -/
theorem removable_singularity_abelian {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (ball c R \ {c}))
    (hb : ∃ C : ℝ, ∀ z ∈ ball c R \ {c}, ‖f z‖ ≤ C) :
    DifferentiableOn ℂ (Function.update f c (limUnder (𝓝[≠] c) f)) (ball c R) := by
  obtain ⟨C, hC⟩ := hb
  refine Complex.differentiableOn_update_limUnder_of_bddAbove (Metric.ball_mem_nhds c hR) hd ?_
  refine ⟨C, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact hC z hz

end Frontier

section AxiomCheck
#print axioms Frontier.uhlenbeck_bubbling
#print axioms Frontier.energyOn_rescale
#print axioms Frontier.zero_mem_bubbleSet_rescale
#print axioms Frontier.removable_singularity_abelian
#print axioms Frontier.energyOn_diff_singleton
#print axioms Frontier.bubbleSet_eq_empty_of_energy_lt
end AxiomCheck

