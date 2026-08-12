/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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

namespace Math2

open Filter Topology

/-! ## The Sato–Tate measure -/

/-- The density of the Sato–Tate measure `(2/π) sin²θ dθ` on `[0, π]`. -/
noncomputable def satoTateDensity (x : ℝ) : ℝ := (2 / Real.pi) * Real.sin x ^ 2

/-- An antiderivative of `satoTateDensity`: `F x = (x - sin x cos x)/π`. -/
noncomputable def satoTateCDF (x : ℝ) : ℝ := (x - Real.sin x * Real.cos x) / Real.pi

lemma satoTateDensity_nonneg (x : ℝ) : 0 ≤ satoTateDensity x := by
  have := Real.pi_pos
  have : (0:ℝ) ≤ 2 / Real.pi := by positivity
  unfold satoTateDensity
  positivity

lemma continuous_satoTateDensity : Continuous satoTateDensity := by
  unfold satoTateDensity; fun_prop

lemma continuous_satoTateCDF : Continuous satoTateCDF := by
  unfold satoTateCDF; fun_prop

/-- The fundamental theorem of calculus for the Sato–Tate density. -/
lemma integral_satoTateDensity (a b : ℝ) :
    ∫ x in a..b, satoTateDensity x = satoTateCDF b - satoTateCDF a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    have h1 : HasDerivAt (fun y : ℝ => y - Real.sin y * Real.cos y)
        (1 - (Real.cos x * Real.cos x + Real.sin x * -Real.sin x)) x :=
      (hasDerivAt_id x).sub ((Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x))
    have h2 := h1.div_const Real.pi
    convert h2 using 1
    unfold satoTateDensity
    have hpi := Real.pi_ne_zero
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq x]
  · exact (continuous_satoTateDensity).intervalIntegrable _ _

lemma satoTateCDF_mono : Monotone satoTateCDF := by
  intro x y hxy
  have h := integral_satoTateDensity x y
  have hnn : 0 ≤ ∫ t in x..y, satoTateDensity t :=
    intervalIntegral.integral_nonneg hxy (fun t _ => satoTateDensity_nonneg t)
  linarith [h ▸ hnn]

/-- The Sato–Tate measure is a probability measure on `[0, π]`. -/
theorem satoTate_total_mass : ∫ x in (0:ℝ)..Real.pi, satoTateDensity x = 1 := by
  rw [integral_satoTateDensity]
  unfold satoTateCDF
  simp [Real.pi_ne_zero]

/-! ## Frobenius angles of an elliptic curve -/

/-- Primes below `N`. -/
def primesBelow (N : ℕ) : Finset ℕ := (Finset.range N).filter Nat.Prime

/-- The trace of Frobenius `a_p = p + 1 - #E(𝔽_p)` of an integral Weierstrass curve at `p`,
where `#E(𝔽_p)` counts the affine points together with the point at infinity. -/
noncomputable def frobeniusTrace (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  (p : ℤ) + 1 - (Nat.card ((W.map (Int.castRingHom (ZMod p))).toAffine.Point) : ℤ)

/-- The Frobenius angle `θ_p ∈ [0, π]` defined by `a_p = 2√p cos θ_p`. -/
noncomputable def frobeniusAngle (W : WeierstrassCurve ℤ) (p : ℕ) : ℝ :=
  Real.arccos ((frobeniusTrace W p : ℝ) / (2 * Real.sqrt p))

/-- Sato–Tate equidistribution of a sequence of angles, in Weyl (test-function) form:
the averages of `f (θ p)` over the primes `p < N` converge to the integral of `f`
against the Sato–Tate measure `(2/π) sin²θ dθ` on `[0, π]`. -/
def SatoTateEquidistributed (theta : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f →
    Tendsto (fun N : ℕ => (∑ p ∈ primesBelow N, f (theta p)) / ((primesBelow N).card : ℝ))
      atTop (𝓝 (∫ x in (0:ℝ)..Real.pi, f x * satoTateDensity x))

/-- The Sato–Tate conjecture (a theorem of Clozel–Harris–Shepherd-Barron–Taylor for
non-CM elliptic curves over `ℚ`): the Frobenius angles of `W` are Sato–Tate
equidistributed. -/
def SatoTateHolds (W : WeierstrassCurve ℤ) : Prop :=
  SatoTateEquidistributed (frobeniusAngle W)

/-! ## Tent functions -/

/-- A continuous trapezoidal ("tent") function: it vanishes outside `[c, d]`,
equals `1` on `[c + δ, d - δ]`, and takes values in `[0,1]`. -/
noncomputable def tent (c d delta x : ℝ) : ℝ :=
  min 1 (max 0 (min ((x - c) / delta) ((d - x) / delta)))

lemma continuous_tent (c d delta : ℝ) : Continuous (tent c d delta) := by
  unfold tent; fun_prop

lemma tent_nonneg (c d delta x : ℝ) : 0 ≤ tent c d delta x :=
  le_min zero_le_one (le_max_left _ _)

lemma tent_le_one (c d delta x : ℝ) : tent c d delta x ≤ 1 := min_le_left _ _

lemma tent_eq_one {c d delta x : ℝ} (h : 0 < delta) (h1 : c + delta ≤ x) (h2 : x ≤ d - delta) :
    tent c d delta x = 1 := by
  have h3 : 1 ≤ min ((x - c) / delta) ((d - x) / delta) :=
    le_min (by rw [le_div_iff₀ h]; linarith) (by rw [le_div_iff₀ h]; linarith)
  unfold tent
  rw [max_eq_right (le_trans zero_le_one h3), min_eq_left h3]

lemma tent_eq_zero_left {c d delta x : ℝ} (h : 0 < delta) (h1 : x ≤ c) :
    tent c d delta x = 0 := by
  have h3 : min ((x - c) / delta) ((d - x) / delta) ≤ 0 :=
    le_trans (min_le_left _ _) (div_nonpos_of_nonpos_of_nonneg (by linarith) h.le)
  unfold tent
  rw [max_eq_left h3, min_eq_right zero_le_one]

lemma tent_eq_zero_right {c d delta x : ℝ} (h : 0 < delta) (h1 : d ≤ x) :
    tent c d delta x = 0 := by
  have h3 : min ((x - c) / delta) ((d - x) / delta) ≤ 0 :=
    le_trans (min_le_right _ _) (div_nonpos_of_nonpos_of_nonneg (by linarith) h.le)
  unfold tent
  rw [max_eq_left h3, min_eq_right zero_le_one]

/-! ## Comparison of the tent integrals with the Sato–Tate measure -/

lemma integral_tent_upper {a b delta : ℝ} (hd : 0 < delta) (h0 : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ Real.pi) :
    (∫ x in (0:ℝ)..Real.pi, tent (a - delta) (b + delta) delta x * satoTateDensity x)
      ≤ satoTateCDF (b + delta) - satoTateCDF (a - delta) := by
  have hpi := Real.pi_pos
  set c : ℝ := a - delta with hc
  set d : ℝ := b + delta with hdd
  set g : ℝ → ℝ := fun x => tent c d delta x * satoTateDensity x with hg
  have hgc : Continuous g := (continuous_tent c d delta).mul continuous_satoTateDensity
  have hint : ∀ u v : ℝ, IntervalIntegrable g MeasureTheory.volume u v :=
    fun u v => hgc.intervalIntegrable u v
  set a1 : ℝ := max 0 c with ha1
  set b1 : ℝ := min Real.pi d with hb1
  have h0a1 : (0:ℝ) ≤ a1 := le_max_left _ _
  have ha1b1 : a1 ≤ b1 :=
    max_le (le_min hpi.le (by simp [hdd]; linarith)) (le_min (by simp [hc]; linarith)
      (by simp [hc, hdd]; linarith))
  have hb1pi : b1 ≤ Real.pi := min_le_left _ _
  have hsplit : (∫ x in (0:ℝ)..Real.pi, g x)
      = (∫ x in (0:ℝ)..a1, g x) + (∫ x in a1..b1, g x) + (∫ x in b1..Real.pi, g x) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint 0 a1) (hint a1 b1),
      intervalIntegral.integral_add_adjacent_intervals (hint 0 b1) (hint b1 Real.pi)]
  have hleft : (∫ x in (0:ℝ)..a1, g x) = 0 := by
    rcases le_or_gt c 0 with hcle | hcpos
    · have : a1 = 0 := by simp [ha1, max_eq_left hcle]
      rw [this, intervalIntegral.integral_same]
    · have ha1c : a1 = c := max_eq_right hcpos.le
      rw [show (fun x => g x) = g from rfl]
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_, intervalIntegral.integral_zero]
      intro x hx
      rw [ha1c] at hx
      rw [Set.uIcc_of_le hcpos.le] at hx
      simp [tent_eq_zero_left hd hx.2]
  have hright : (∫ x in b1..Real.pi, g x) = 0 := by
    rcases le_or_gt Real.pi d with hdge | hdlt
    · have : b1 = Real.pi := min_eq_left hdge
      rw [this, intervalIntegral.integral_same]
    · have hb1d : b1 = d := min_eq_right hdlt.le
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_, intervalIntegral.integral_zero]
      intro x hx
      rw [hb1d] at hx
      rw [Set.uIcc_of_le hdlt.le] at hx
      simp [hg, tent_eq_zero_right hd hx.1]
  have hmid : (∫ x in a1..b1, g x) ≤ satoTateCDF b1 - satoTateCDF a1 := by
    rw [← integral_satoTateDensity]
    refine intervalIntegral.integral_mono_on ha1b1 (hint a1 b1)
      (continuous_satoTateDensity.intervalIntegrable _ _) ?_
    intro x _
    have h1 : tent c d delta x ≤ 1 := tent_le_one _ _ _ _
    have h2 : 0 ≤ satoTateDensity x := satoTateDensity_nonneg x
    calc tent c d delta x * satoTateDensity x ≤ 1 * satoTateDensity x := by nlinarith
      _ = satoTateDensity x := one_mul _
  have hmono1 : satoTateCDF b1 ≤ satoTateCDF d := satoTateCDF_mono (min_le_right _ _)
  have hmono2 : satoTateCDF c ≤ satoTateCDF a1 := satoTateCDF_mono (le_max_right _ _)
  rw [hsplit, hleft, hright]
  linarith

lemma integral_tent_lower {a b delta : ℝ} (hd : 0 < delta) (h0 : 0 ≤ a)
    (hb : b ≤ Real.pi) :
    satoTateCDF (b - delta) - satoTateCDF (a + delta)
      ≤ ∫ x in (0:ℝ)..Real.pi, tent a b delta x * satoTateDensity x := by
  have hpi := Real.pi_pos
  set g : ℝ → ℝ := fun x => tent a b delta x * satoTateDensity x with hg
  have hgc : Continuous g := (continuous_tent a b delta).mul continuous_satoTateDensity
  have hint : ∀ u v : ℝ, IntervalIntegrable g MeasureTheory.volume u v :=
    fun u v => hgc.intervalIntegrable u v
  have hgnn : ∀ x, 0 ≤ g x := fun x =>
    mul_nonneg (tent_nonneg _ _ _ _) (satoTateDensity_nonneg x)
  rcases le_or_gt (a + delta) (b - delta) with hle | hlt
  · have h0u : (0:ℝ) ≤ a + delta := by linarith
    have hvpi : b - delta ≤ Real.pi := by linarith
    have hsplit : (∫ x in (0:ℝ)..Real.pi, g x)
        = (∫ x in (0:ℝ)..(a + delta), g x) + (∫ x in (a + delta)..(b - delta), g x)
          + (∫ x in (b - delta)..Real.pi, g x) := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hint 0 _) (hint _ _),
        intervalIntegral.integral_add_adjacent_intervals (hint 0 _) (hint _ Real.pi)]
    have h1 : 0 ≤ ∫ x in (0:ℝ)..(a + delta), g x :=
      intervalIntegral.integral_nonneg h0u (fun t _ => hgnn t)
    have h3 : 0 ≤ ∫ x in (b - delta)..Real.pi, g x :=
      intervalIntegral.integral_nonneg hvpi (fun t _ => hgnn t)
    have h2 : (∫ x in (a + delta)..(b - delta), g x)
        = satoTateCDF (b - delta) - satoTateCDF (a + delta) := by
      rw [← integral_satoTateDensity]
      refine intervalIntegral.integral_congr ?_
      intro x hx
      have hx' : a + delta ≤ x ∧ x ≤ b - delta := by
        rw [Set.uIcc_of_le hle] at hx; exact ⟨hx.1, hx.2⟩
      simp [hg, tent_eq_one hd hx'.1 hx'.2]
    rw [hsplit, h2]
    linarith
  · have : satoTateCDF (b - delta) ≤ satoTateCDF (a + delta) := satoTateCDF_mono hlt.le
    have h4 : 0 ≤ ∫ x in (0:ℝ)..Real.pi, g x :=
      intervalIntegral.integral_nonneg hpi.le (fun t _ => hgnn t)
    linarith

/-! ## Counting comparison -/

lemma sum_tent_le_card {theta : ℕ → ℝ} {a b delta : ℝ} (hd : 0 < delta) (N : ℕ) :
    (∑ p ∈ primesBelow N, tent a b delta (theta p))
      ≤ (((primesBelow N).filter (fun p => theta p ∈ Set.Icc a b)).card : ℝ) := by
  classical
  rw [← Finset.sum_boole (fun p => theta p ∈ Set.Icc a b) (primesBelow N)]
  refine Finset.sum_le_sum ?_
  intro p _
  by_cases hp : theta p ∈ Set.Icc a b
  · rw [if_pos hp]; exact tent_le_one _ _ _ _
  · rw [if_neg hp]
    simp only [Set.mem_Icc, not_and_or, not_le] at hp
    rcases hp with h1 | h1
    · exact le_of_eq (tent_eq_zero_left hd h1.le)
    · exact le_of_eq (tent_eq_zero_right hd h1.le)

lemma card_le_sum_tent {theta : ℕ → ℝ} {a b delta : ℝ} (hd : 0 < delta) (N : ℕ) :
    (((primesBelow N).filter (fun p => theta p ∈ Set.Icc a b)).card : ℝ)
      ≤ ∑ p ∈ primesBelow N, tent (a - delta) (b + delta) delta (theta p) := by
  classical
  rw [← Finset.sum_boole (fun p => theta p ∈ Set.Icc a b) (primesBelow N)]
  refine Finset.sum_le_sum ?_
  intro p _
  by_cases hp : theta p ∈ Set.Icc a b
  · rw [if_pos hp]
    rw [Set.mem_Icc] at hp
    exact le_of_eq (tent_eq_one hd (by linarith [hp.1]) (by linarith [hp.2])).symm
  · rw [if_neg hp]
    exact tent_nonneg _ _ _ _

/-! ## The main theorem -/

/-- **The Sato–Tate distribution of Frobenius angles.**

Let `W` be an integral Weierstrass model of an elliptic curve and let
`θ_p = arccos (a_p / (2√p))` be its Frobenius angles, where `a_p = p + 1 - #E(𝔽_p)`.
Assume the Sato–Tate equidistribution law (`SatoTateHolds W`), stated in Weyl form for
continuous test functions; by the theorem of Clozel–Harris–Shepherd-Barron–Taylor this
holds for every elliptic curve over `ℚ` without complex multiplication.

Then, for every subinterval `[α, β] ⊆ [0, π]`, the natural density of the primes whose
Frobenius angle lies in `[α, β]` exists and equals the Sato–Tate measure of `[α, β]`:
`(2/π) ∫_α^β sin²θ dθ`. -/
theorem sato_tate (W : WeierstrassCurve ℤ) (hST : SatoTateHolds W)
    {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi) :
    Tendsto (fun N : ℕ =>
        (((primesBelow N).filter (fun p => frobeniusAngle W p ∈ Set.Icc a b)).card : ℝ)
          / ((primesBelow N).card : ℝ))
      atTop (𝓝 (∫ x in a..b, satoTateDensity x)) := by
  classical
  rw [integral_satoTateDensity, Metric.tendsto_atTop]
  intro eps heps
  -- choose `delta` so that the Sato–Tate mass of the `delta`-collars is small
  obtain ⟨d1, hd1pos, hd1⟩ :=
    Metric.continuousAt_iff.mp (continuous_satoTateCDF.continuousAt (x := a)) (eps / 4)
      (by linarith)
  obtain ⟨d2, hd2pos, hd2⟩ :=
    Metric.continuousAt_iff.mp (continuous_satoTateCDF.continuousAt (x := b)) (eps / 4)
      (by linarith)
  set delta : ℝ := min d1 d2 / 2 with hdelta
  have hdpos : 0 < delta := by
    have := lt_min hd1pos hd2pos
    simp only [hdelta]
    linarith
  have hdd1 : delta < d1 := by
    have h := min_le_left d1 d2
    simp only [hdelta]
    linarith
  have hdd2 : delta < d2 := by
    have h := min_le_right d1 d2
    simp only [hdelta]
    linarith
  have hFa1 : |satoTateCDF (a - delta) - satoTateCDF a| < eps / 4 := by
    have := hd1 (x := a - delta) (by simp [abs_of_pos hdpos]; linarith)
    simpa [Real.dist_eq] using this
  have hFa2 : |satoTateCDF (a + delta) - satoTateCDF a| < eps / 4 := by
    have := hd1 (x := a + delta) (by simp [abs_of_pos hdpos]; linarith)
    simpa [Real.dist_eq] using this
  have hFb1 : |satoTateCDF (b - delta) - satoTateCDF b| < eps / 4 := by
    have := hd2 (x := b - delta) (by simp [abs_of_pos hdpos]; linarith)
    simpa [Real.dist_eq] using this
  have hFb2 : |satoTateCDF (b + delta) - satoTateCDF b| < eps / 4 := by
    have := hd2 (x := b + delta) (by simp [abs_of_pos hdpos]; linarith)
    simpa [Real.dist_eq] using this
  rw [abs_lt] at hFa1 hFa2 hFb1 hFb2
  -- the two test functions
  set gl : ℝ → ℝ := tent a b delta with hgl
  set gu : ℝ → ℝ := tent (a - delta) (b + delta) delta with hgu
  have hlim_l := hST gl (continuous_tent _ _ _)
  have hlim_u := hST gu (continuous_tent _ _ _)
  rw [Metric.tendsto_atTop] at hlim_l hlim_u
  obtain ⟨N1, hN1⟩ := hlim_l (eps / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := hlim_u (eps / 2) (by linarith)
  refine ⟨max N1 N2, fun N hN => ?_⟩
  have hN1' := hN1 N (le_trans (le_max_left _ _) hN)
  have hN2' := hN2 N (le_trans (le_max_right _ _) hN)
  rw [Real.dist_eq, abs_lt] at hN1' hN2' ⊢
  set S : Finset ℕ := primesBelow N with hS
  set C : ℝ := (((primesBelow N).filter
    (fun p => frobeniusAngle W p ∈ Set.Icc a b)).card : ℝ) with hC
  have hcard_nonneg : (0:ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hlow : (∑ p ∈ S, gl (frobeniusAngle W p)) / (S.card : ℝ) ≤ C / (S.card : ℝ) := by
    have := sum_tent_le_card (theta := frobeniusAngle W) (a := a) (b := b) hdpos N
    gcongr
  have hupp : C / (S.card : ℝ) ≤ (∑ p ∈ S, gu (frobeniusAngle W p)) / (S.card : ℝ) := by
    have := card_le_sum_tent (theta := frobeniusAngle W) (a := a) (b := b) hdpos N
    gcongr
  have hIu : (∫ x in (0:ℝ)..Real.pi, gu x * satoTateDensity x)
      ≤ satoTateCDF (b + delta) - satoTateCDF (a - delta) := integral_tent_upper hdpos h0 hab hb
  have hIl : satoTateCDF (b - delta) - satoTateCDF (a + delta)
      ≤ ∫ x in (0:ℝ)..Real.pi, gl x * satoTateDensity x := integral_tent_lower hdpos h0 hb
  constructor
  · linarith [hN1'.1, hlow]
  · linarith [hN2'.2, hupp]

/-- The same statement with the Sato–Tate measure of `[a, b]` written out explicitly:
`(2/π) ∫_a^b sin²θ dθ = ((b - sin b cos b) - (a - sin a cos a))/π`. -/
theorem sato_tate_explicit (W : WeierstrassCurve ℤ) (hST : SatoTateHolds W)
    {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi) :
    Tendsto (fun N : ℕ =>
        (((primesBelow N).filter (fun p => frobeniusAngle W p ∈ Set.Icc a b)).card : ℝ)
          / ((primesBelow N).card : ℝ))
      atTop (𝓝 (((b - Real.sin b * Real.cos b) - (a - Real.sin a * Real.cos a)) / Real.pi)) := by
  have h := sato_tate W hST h0 hab hb
  rwa [integral_satoTateDensity,
    show satoTateCDF b - satoTateCDF a
      = ((b - Real.sin b * Real.cos b) - (a - Real.sin a * Real.cos a)) / Real.pi by
        unfold satoTateCDF; ring] at h

end Math2

