import Mathlib
import RequestProject.SatoTate.Equidistribution

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above is placed directly after the `import` lines, since Lean 4 requires
`import` commands to come first in a file.)

## Contents

We formalise the Sato–Tate distribution of Frobenius angles of an elliptic curve over `ℚ`,
given by an integral Weierstrass model `W`.

* `Math2.frobAngle W p` is the Frobenius angle `θ_p ∈ [0, π]` at a prime `p`, defined by
  `a_p = 2 √p cos θ_p` where `a_p = p + 1 - #E(𝔽_p)` is the trace of Frobenius.
* `Math2.satoTateDensity` is the Sato–Tate density `(2/π) sin²θ` and `Math2.satoTateMeasure`
  is the associated probability measure on `[0, π]`.
* `Math2.SatoTateWeyl W` is the Weyl-criterion form of the Sato–Tate law: the averages over
  primes of good reduction of `U n (cos θ_p)` tend to `0` for every `n ≥ 1`, where `U n` is
  the `n`-th Chebyshev polynomial of the second kind (the character of the `n`-th symmetric
  power of the standard representation of `SU(2)`).  This is exactly the statement supplied
  by the potential automorphy theorems for a non-CM elliptic curve over `ℚ`.
* `Math2.sato_tate` deduces from it the distributional form of the Sato–Tate law: the
  proportion of primes `p ≤ N` of good reduction whose Frobenius angle lies in `[a, b]`
  converges to `(2/π) ∫_a^b sin²t dt`.
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

set_option grind.warning false

namespace Math2

open Filter Topology MeasureTheory Set

/-- The number of points of the reduction of the integral Weierstrass model `W` modulo `p`
(including the point at infinity). -/
noncomputable def pointCount (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card (W.map (Int.castRingHom (ZMod p))).toAffine.Point

/-- The trace of Frobenius `a_p = p + 1 - #E(𝔽_p)`. -/
noncomputable def frobTrace (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  (p : ℤ) + 1 - (pointCount W p : ℤ)

/-- The Frobenius angle `θ_p ∈ [0, π]`, defined by `a_p = 2 √p cos θ_p`; this is well defined
by the Hasse bound `|a_p| ≤ 2 √p`. -/
noncomputable def frobAngle (W : WeierstrassCurve ℤ) (p : ℕ) : ℝ :=
  Real.arccos ((frobTrace W p : ℝ) / (2 * Real.sqrt p))

lemma frobAngle_mem_Icc (W : WeierstrassCurve ℤ) (p : ℕ) : frobAngle W p ∈ Icc 0 π :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- The primes `p ≤ N` at which the integral model `W` has good reduction. -/
noncomputable def goodPrimesBelow (W : WeierstrassCurve ℤ) (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun p => p.Prime ∧ ¬ ((p : ℤ) ∣ W.Δ))

/-- The thirteen `j`-invariants of elliptic curves over `ℚ` admitting complex multiplication
(the `j`-invariants of the imaginary quadratic orders of class number one). -/
def cmJInvariants : Finset ℚ :=
  {0, 54000, -12288000, 1728, 287496, -3375, 16581375, 8000, -32768, -884736, -884736000,
    -147197952000, -262537412640768000}

/-- `W` has complex multiplication, i.e. its `j`-invariant `c₄³ / Δ` is one of the thirteen
rational CM `j`-invariants. -/
def HasCM (W : WeierstrassCurve ℤ) : Prop :=
  ∃ j ∈ cmJInvariants, j * (W.Δ : ℚ) = (W.c₄ : ℚ) ^ 3

/-- The Weyl-criterion (equivalently, symmetric-power) form of the Sato–Tate law for `W`:
for every `n ≥ 1` the averages over the primes of good reduction `p ≤ N` of
`U n (cos θ_p)` tend to `0`, where `U n` is the `n`-th Chebyshev polynomial of the second
kind.  For a non-CM elliptic curve over `ℚ` this is the content of the potential automorphy
theorems of Taylor et al. -/
def SatoTateWeyl (W : WeierstrassCurve ℤ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    Tendsto (fun N : ℕ => avg (goodPrimesBelow W N) (frobAngle W)
      (fun t => (Polynomial.Chebyshev.U ℝ n).eval (Real.cos t))) atTop (𝓝 0)

lemma goodPrimesBelow_eventually_nonempty {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0) :
    ∀ᶠ N in atTop, (goodPrimesBelow W N).Nonempty := by
  obtain ⟨p₀, hp₀ge, hp₀prime⟩ := Nat.exists_infinite_primes (W.Δ.natAbs + 1)
  have hndvd : ¬ ((p₀ : ℤ) ∣ W.Δ) := by
    intro hdvd
    have h1 : (p₀ : ℤ) ≤ |W.Δ| := Int.le_of_dvd (abs_pos.mpr hΔ) ((dvd_abs _ _).mpr hdvd)
    rw [Int.abs_eq_natAbs] at h1
    have h2 : p₀ ≤ W.Δ.natAbs := by exact_mod_cast h1
    omega
  filter_upwards [Filter.eventually_ge_atTop p₀] with N hN
  refine ⟨p₀, ?_⟩
  simp only [goodPrimesBelow, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hp₀prime, hndvd⟩

/-- **The Sato–Tate distribution of Frobenius angles.**

Let `E` be an elliptic curve over `ℚ` given by an integral Weierstrass model `W` with
non-vanishing discriminant, and assume `E` has no complex multiplication.  Granting the
Weyl-criterion form `SatoTateWeyl W` of the Sato–Tate law (the input provided by the
automorphy of the symmetric power `L`-functions of a non-CM elliptic curve), the Frobenius
angles `θ_p ∈ [0, π]`, defined by `a_p = 2√p cos θ_p`, are equidistributed with respect to the
Sato–Tate measure: for `0 ≤ a ≤ b ≤ π` the proportion of primes of good reduction `p ≤ N`
with `θ_p ∈ [a, b]` converges to `(2/π) ∫_a^b sin² t dt`.

The non-CM hypothesis `hCM` is not used in this deduction: it is what guarantees the
hypothesis `hST` (for a CM curve the angles obey a different, non-Sato–Tate law). -/
theorem sato_tate (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hCM : ¬ HasCM W)
    (hST : SatoTateWeyl W) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π) :
    Tendsto (fun N : ℕ =>
        (((goodPrimesBelow W N).filter (fun p => frobAngle W p ∈ Icc a b)).card : ℝ)
          / ((goodPrimesBelow W N).card : ℝ))
      atTop (𝓝 (∫ t in a..b, 2 / π * Real.sin t ^ 2)) :=
  tendsto_count_of_chebyshev (frobAngle_mem_Icc W)
    (goodPrimesBelow_eventually_nonempty hΔ) hST ha hab hb

/-- A concrete instance of the Sato–Tate law: the Frobenius angles are as often in the first
half `[0, π/2]` of the range as in the second, i.e. the traces of Frobenius `a_p` are
non-negative for half of the primes. -/
theorem sato_tate_half (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hCM : ¬ HasCM W)
    (hST : SatoTateWeyl W) :
    Tendsto (fun N : ℕ =>
        (((goodPrimesBelow W N).filter (fun p => frobAngle W p ∈ Icc 0 (π / 2))).card : ℝ)
          / ((goodPrimesBelow W N).card : ℝ))
      atTop (𝓝 (1 / 2)) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hval : ∫ t in (0:ℝ)..(π / 2), 2 / π * Real.sin t ^ 2 = 1 / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_sin_sq]
    simp only [Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two]
    field_simp
    ring
  have := sato_tate W hΔ hCM hST (a := 0) (b := π / 2) le_rfl (by positivity) (by linarith)
  rwa [hval] at this

end Math2

import RequestProject.SatoTate.Chebyshev

/-!
# From the Weyl criterion to equidistribution for the Sato–Tate measure

This file contains the analytic heart of the Sato–Tate statement: if the averages of the
Chebyshev polynomials `U n` (`n ≥ 1`) evaluated at a family of angles tend to `0`, then the
angles are equidistributed with respect to the Sato–Tate measure `(2/π) sin²θ dθ`.
-/

open MeasureTheory Real Set Filter Topology
open scoped Classical

namespace Math2

/-- The average of `f ∘ θ` over the finite index set `S`. -/
noncomputable def avg (S : Finset ℕ) (θ : ℕ → ℝ) (f : ℝ → ℝ) : ℝ :=
  (∑ p ∈ S, f (θ p)) / S.card

lemma avg_add (S : Finset ℕ) (θ : ℕ → ℝ) (f g : ℝ → ℝ) :
    avg S θ (fun t => f t + g t) = avg S θ f + avg S θ g := by
  unfold avg; rw [← add_div, Finset.sum_add_distrib]

lemma avg_const_mul (S : Finset ℕ) (θ : ℕ → ℝ) (c : ℝ) (f : ℝ → ℝ) :
    avg S θ (fun t => c * f t) = c * avg S θ f := by
  rw [avg, avg, ← Finset.mul_sum, mul_div_assoc]

lemma avg_const (S : Finset ℕ) (θ : ℕ → ℝ) (c : ℝ) (hS : S.Nonempty) :
    avg S θ (fun _ => c) = c := by
  have : (S.card : ℝ) ≠ 0 := by
    simp [Finset.card_ne_zero_of_mem hS.choose_spec]
  unfold avg
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

lemma avg_mono {S : Finset ℕ} {θ : ℕ → ℝ} {f g : ℝ → ℝ} (h : ∀ t, f t ≤ g t) :
    avg S θ f ≤ avg S θ g := by
  unfold avg
  gcongr with p hp
  exact h (θ p)

/-- A bound on the difference of averages of two uniformly close functions. -/
lemma abs_avg_sub_avg_le {S : Finset ℕ} {θ : ℕ → ℝ} {f g : ℝ → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ p ∈ S, |f (θ p) - g (θ p)| ≤ ε) : |avg S θ f - avg S θ g| ≤ ε := by
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · simp [avg, hε]
  have hcard : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hSne
  unfold avg
  rw [div_sub_div_same, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hcard, div_le_iff₀ hcard]
  calc |∑ p ∈ S, (f (θ p) - g (θ p))| ≤ ∑ p ∈ S, |f (θ p) - g (θ p)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ S, ε := Finset.sum_le_sum h
    _ = ε * S.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- A continuous trapezoidal function: it equals `1` on `[a + e, b - e]`, vanishes outside
`[a, b]`, and interpolates linearly in between. -/
noncomputable def trapezoid (a b e : ℝ) (t : ℝ) : ℝ :=
  max 0 (min 1 (min ((t - a) / e) ((b - t) / e)))

lemma continuous_trapezoid (a b e : ℝ) : Continuous (trapezoid a b e) := by
  unfold trapezoid; fun_prop

lemma trapezoid_nonneg (a b e t : ℝ) : 0 ≤ trapezoid a b e t := le_max_left _ _

lemma trapezoid_le_one (a b e t : ℝ) : trapezoid a b e t ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

lemma trapezoid_eq_zero {a b e t : ℝ} (he : 0 < e) (h : t < a ∨ b < t) :
    trapezoid a b e t = 0 := by
  have hneg : min ((t - a) / e) ((b - t) / e) < 0 := by
    rcases h with h | h
    · exact lt_of_le_of_lt (min_le_left _ _) (div_neg_of_neg_of_pos (by linarith) he)
    · exact lt_of_le_of_lt (min_le_right _ _) (div_neg_of_neg_of_pos (by linarith) he)
  have h2 : min 1 (min ((t - a) / e) ((b - t) / e)) < 0 := lt_of_le_of_lt (min_le_right _ _) hneg
  simp [trapezoid, max_eq_left h2.le]

lemma trapezoid_eq_one {a b e t : ℝ} (he : 0 < e) (h1 : a + e ≤ t) (h2 : t ≤ b - e) :
    trapezoid a b e t = 1 := by
  have hA : (1:ℝ) ≤ (t - a) / e := (le_div_iff₀ he).2 (by linarith)
  have hB : (1:ℝ) ≤ (b - t) / e := (le_div_iff₀ he).2 (by linarith)
  have : min 1 (min ((t - a) / e) ((b - t) / e)) = 1 := min_eq_left (le_min hA hB)
  simp [trapezoid, this]

lemma trapezoid_le_indicator {a b e : ℝ} (he : 0 < e) (t : ℝ) :
    trapezoid a b e t ≤ Set.indicator (Icc a b) (1 : ℝ → ℝ) t := by
  by_cases ht : t ∈ Icc a b
  · rw [Set.indicator_of_mem ht]
    exact trapezoid_le_one _ _ _ _
  · rw [Set.indicator_of_notMem ht]
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    exact le_of_eq (trapezoid_eq_zero he (by tauto))

lemma indicator_le_trapezoid {a b a' b' e : ℝ} (he : 0 < e) (ha : a' + e ≤ a) (hb : b ≤ b' - e)
    (t : ℝ) : Set.indicator (Icc a b) (1 : ℝ → ℝ) t ≤ trapezoid a' b' e t := by
  by_cases ht : t ∈ Icc a b
  · rw [Set.indicator_of_mem ht, trapezoid_eq_one he (le_trans ha ht.1) (le_trans ht.2 hb)]
    simp
  · rw [Set.indicator_of_notMem ht]
    exact trapezoid_nonneg _ _ _ _

lemma indicator_sub_trapezoid_le {a b e : ℝ} (he : 0 < e) (t : ℝ) :
    Set.indicator (Icc a b) (1 : ℝ → ℝ) t - trapezoid a b e t
      ≤ Set.indicator (Icc a (a + e)) (1 : ℝ → ℝ) t
        + Set.indicator (Icc (b - e) b) (1 : ℝ → ℝ) t := by
  have hnn1 : (0:ℝ) ≤ Set.indicator (Icc a (a + e)) (1 : ℝ → ℝ) t :=
    Set.indicator_nonneg (by intro x _; norm_num) t
  have hnn2 : (0:ℝ) ≤ Set.indicator (Icc (b - e) b) (1 : ℝ → ℝ) t :=
    Set.indicator_nonneg (by intro x _; norm_num) t
  by_cases ht : t ∈ Icc a b
  · rw [Set.indicator_of_mem ht]
    by_cases hin : a + e ≤ t ∧ t ≤ b - e
    · rw [trapezoid_eq_one he hin.1 hin.2]
      simpa using add_nonneg hnn1 hnn2
    · have hle : (1:ℝ) - trapezoid a b e t ≤ 1 := by
        have := trapezoid_nonneg a b e t; linarith
      rcases not_and_or.1 hin with h | h
      · have hmem : t ∈ Icc a (a + e) := ⟨ht.1, le_of_lt (not_le.1 h)⟩
        rw [Set.indicator_of_mem hmem]
        simp only [Pi.one_apply]
        linarith
      · have hmem : t ∈ Icc (b - e) b := ⟨le_of_lt (not_le.1 h), ht.2⟩
        rw [Set.indicator_of_mem hmem]
        simp only [Pi.one_apply]
        linarith
  · rw [Set.indicator_of_notMem ht]
    have := trapezoid_nonneg a b e t
    linarith

lemma avg_indicator (S : Finset ℕ) (θ : ℕ → ℝ) (a b : ℝ) :
    avg S θ (Set.indicator (Icc a b) (1 : ℝ → ℝ))
      = ((S.filter (fun p => θ p ∈ Icc a b)).card : ℝ) / S.card := by
  unfold avg
  congr 1
  simp [Set.indicator_apply]

lemma satoTateMeasure_real_Icc_le {x y : ℝ} (h : x ≤ y) :
    satoTateMeasure.real (Icc x y) ≤ 2 / π * (y - x) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hbound : satoTateMeasure (Icc x y) ≤ ENNReal.ofReal (2 / π * (y - x)) := by
    calc satoTateMeasure (Icc x y) ≤ ENNReal.ofReal (2 / π) * volume (Icc x y) :=
          satoTateMeasure_le_volume _
      _ = ENNReal.ofReal (2 / π) * ENNReal.ofReal (y - x) := by rw [Real.volume_Icc]
      _ = ENNReal.ofReal (2 / π * (y - x)) := (ENNReal.ofReal_mul (by positivity)).symm
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (by positivity) (by linarith)) hbound

section Equidistribution

variable {S : ℕ → Finset ℕ} {θ : ℕ → ℝ}

/-- Averages against polynomials in `cos θ` converge to the corresponding Sato–Tate integral. -/
theorem tendsto_avg_polynomial
    (hS : ∀ᶠ N in atTop, (S N).Nonempty)
    (hU : ∀ n : ℕ, 1 ≤ n →
      Tendsto (fun N => avg (S N) θ
        (fun t => (Polynomial.Chebyshev.U ℝ n).eval (Real.cos t))) atTop (𝓝 0))
    (P : Polynomial ℝ) :
    Tendsto (fun N => avg (S N) θ (fun t => P.eval (Real.cos t))) atTop
      (𝓝 (∫ t, P.eval (Real.cos t) ∂satoTateMeasure)) := by
  refine chebyshevU_span_induction (motive := fun P : Polynomial ℝ =>
    Tendsto (fun N => avg (S N) θ (fun t => P.eval (Real.cos t))) atTop
      (𝓝 (∫ t, P.eval (Real.cos t) ∂satoTateMeasure))) ?_ ?_ ?_ P
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hfun : (fun t : ℝ => (Polynomial.Chebyshev.U ℝ ((0:ℕ) : ℤ)).eval (Real.cos t))
          = fun _ : ℝ => (1:ℝ) := by
        funext t; simp [Polynomial.Chebyshev.U_zero]
      rw [hfun]
      have hint : ∫ _t : ℝ, (1:ℝ) ∂satoTateMeasure = 1 := by simp
      rw [hint]
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hS] with N hN using (avg_const (S N) θ 1 hN).symm
    · rw [integral_chebyshevU_satoTateMeasure n hn]
      exact hU n hn
  · intro c P hP
    have h1 : ∀ t : ℝ, (Polynomial.C c * P).eval (Real.cos t) = c * P.eval (Real.cos t) := by
      intro t; simp
    simp only [h1, avg_const_mul, MeasureTheory.integral_const_mul]
    exact hP.const_mul c
  · intro P Q hP hQ
    have h1 : ∀ t : ℝ, (P + Q).eval (Real.cos t)
        = P.eval (Real.cos t) + Q.eval (Real.cos t) := by
      intro t; simp
    simp only [h1, avg_add]
    rw [MeasureTheory.integral_add (integrable_of_continuous (continuous_eval_cos P))
      (integrable_of_continuous (continuous_eval_cos Q))]
    exact hP.add hQ

/-- Averages against continuous functions converge to the corresponding Sato–Tate integral. -/
theorem tendsto_avg_continuous
    (hθ : ∀ p, θ p ∈ Icc 0 π)
    (hS : ∀ᶠ N in atTop, (S N).Nonempty)
    (hU : ∀ n : ℕ, 1 ≤ n →
      Tendsto (fun N => avg (S N) θ
        (fun t => (Polynomial.Chebyshev.U ℝ n).eval (Real.cos t))) atTop (𝓝 0))
    {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (fun N => avg (S N) θ f) atTop (𝓝 (∫ t, f t ∂satoTateMeasure)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ε : ℝ := δ / 4 with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn (-1) 1
    (fun x => f (Real.arccos x)) (Continuous.continuousOn (by fun_prop)) ε hε
  have hclose : ∀ t ∈ Icc (0:ℝ) π, |P.eval (Real.cos t) - f t| ≤ ε := by
    intro t ht
    have hcos : Real.cos t ∈ Icc (-1:ℝ) 1 := ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩
    have h := hP (Real.cos t) hcos
    rw [Real.arccos_cos ht.1 ht.2] at h
    exact h.le
  have h1 : ∀ N, |avg (S N) θ f - avg (S N) θ (fun t => P.eval (Real.cos t))| ≤ ε := by
    intro N
    refine abs_avg_sub_avg_le hε.le (fun p _ => ?_)
    rw [abs_sub_comm]
    exact hclose (θ p) (hθ p)
  have h2 : |(∫ t, f t ∂satoTateMeasure) - ∫ t, P.eval (Real.cos t) ∂satoTateMeasure| ≤ ε := by
    rw [← MeasureTheory.integral_sub (integrable_of_continuous hf)
      (integrable_of_continuous (continuous_eval_cos P))]
    have hb : ∀ᵐ t ∂satoTateMeasure, ‖f t - P.eval (Real.cos t)‖ ≤ ε := by
      filter_upwards [satoTateMeasure_ae_mem_Icc] with t ht
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hclose t ht
    have := MeasureTheory.norm_integral_le_of_norm_le_const hb
    simpa using this
  have h3 := tendsto_avg_polynomial hS hU P
  rw [Metric.tendsto_atTop] at h3
  obtain ⟨N₀, hN₀⟩ := h3 ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  have hmid := hN₀ N hN
  rw [Real.dist_eq] at hmid ⊢
  have t1 := abs_sub_le (avg (S N) θ f) (avg (S N) θ (fun t => P.eval (Real.cos t)))
    (∫ t, f t ∂satoTateMeasure)
  have t2 := abs_sub_le (avg (S N) θ (fun t => P.eval (Real.cos t)))
    (∫ t, P.eval (Real.cos t) ∂satoTateMeasure) (∫ t, f t ∂satoTateMeasure)
  have h2' : |(∫ t, P.eval (Real.cos t) ∂satoTateMeasure) - ∫ t, f t ∂satoTateMeasure| ≤ ε := by
    rw [abs_sub_comm]; exact h2
  have := h1 N
  linarith

/-- **Equidistribution from the Weyl criterion.** If the Chebyshev averages of a family of
angles in `[0, π]` tend to zero, then the proportion of angles lying in `[a, b]` tends to the
Sato–Tate measure of `[a, b]`, namely `(2/π) ∫_a^b sin²t dt`. -/
theorem tendsto_count_of_chebyshev
    (hθ : ∀ p, θ p ∈ Icc 0 π)
    (hS : ∀ᶠ N in atTop, (S N).Nonempty)
    (hU : ∀ n : ℕ, 1 ≤ n →
      Tendsto (fun N => avg (S N) θ
        (fun t => (Polynomial.Chebyshev.U ℝ n).eval (Real.cos t))) atTop (𝓝 0))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π) :
    Tendsto (fun N => (((S N).filter (fun p => θ p ∈ Icc a b)).card : ℝ) / (S N).card)
      atTop (𝓝 (∫ t in a..b, satoTateDensity t)) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  rw [← satoTateMeasure_Icc_toReal ha hab hb]
  set L : ℝ := (satoTateMeasure (Icc a b)).toReal with hL
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set e : ℝ := δ * π / 16 with hedef
  have he : 0 < e := by positivity
  have hsmall : 2 / π * e = δ / 8 := by rw [hedef]; field_simp; ring
  set g : ℝ → ℝ := trapezoid a b e with hgdef
  set h : ℝ → ℝ := trapezoid (a - e) (b + e) e with hhdef
  have hglim := tendsto_avg_continuous hθ hS hU (continuous_trapezoid a b e)
  have hhlim := tendsto_avg_continuous hθ hS hU (continuous_trapezoid (a - e) (b + e) e)
  -- integrability facts
  have hind : ∀ x y : ℝ, Integrable (Set.indicator (Icc x y) (1 : ℝ → ℝ)) satoTateMeasure :=
    fun x y => (integrable_const (1:ℝ)).indicator measurableSet_Icc
  have hintg : Integrable g satoTateMeasure :=
    integrable_of_continuous (continuous_trapezoid a b e)
  have hinth : Integrable h satoTateMeasure :=
    integrable_of_continuous (continuous_trapezoid (a - e) (b + e) e)
  -- lower bound for the integral of `g`
  have hInt_g : L - δ / 4 ≤ ∫ t, g t ∂satoTateMeasure := by
    have hmono : ∫ t, (Set.indicator (Icc a b) (1 : ℝ → ℝ) t - g t) ∂satoTateMeasure
        ≤ ∫ t, (Set.indicator (Icc a (a + e)) (1 : ℝ → ℝ) t
            + Set.indicator (Icc (b - e) b) (1 : ℝ → ℝ) t) ∂satoTateMeasure :=
      MeasureTheory.integral_mono ((hind a b).sub hintg) ((hind _ _).add (hind _ _))
        (fun t => indicator_sub_trapezoid_le he t)
    rw [MeasureTheory.integral_sub (hind a b) hintg,
      MeasureTheory.integral_add (hind _ _) (hind _ _),
      MeasureTheory.integral_indicator_one measurableSet_Icc,
      MeasureTheory.integral_indicator_one measurableSet_Icc,
      MeasureTheory.integral_indicator_one measurableSet_Icc] at hmono
    have h1 : satoTateMeasure.real (Icc a (a + e)) ≤ δ / 8 := by
      have := satoTateMeasure_real_Icc_le (x := a) (y := a + e) (by linarith)
      rw [← hsmall]; simpa using this
    have h2 : satoTateMeasure.real (Icc (b - e) b) ≤ δ / 8 := by
      have := satoTateMeasure_real_Icc_le (x := b - e) (y := b) (by linarith)
      rw [← hsmall]; simpa using this
    have hLeq : satoTateMeasure.real (Icc a b) = L := rfl
    rw [hLeq] at hmono
    linarith
  -- upper bound for the integral of `h`
  have hInt_h : ∫ t, h t ∂satoTateMeasure ≤ L + δ / 4 := by
    have hmono : ∫ t, h t ∂satoTateMeasure
        ≤ ∫ t, Set.indicator (Icc (a - e) (b + e)) (1 : ℝ → ℝ) t ∂satoTateMeasure :=
      MeasureTheory.integral_mono hinth (hind _ _) (fun t => trapezoid_le_indicator he t)
    rw [MeasureTheory.integral_indicator_one measurableSet_Icc] at hmono
    have hsub : Icc (a - e) (b + e) ⊆ Icc (a - e) a ∪ (Icc a b ∪ Icc b (b + e)) := by
      intro t ht
      rcases le_or_gt t a with h' | h'
      · exact Or.inl ⟨ht.1, h'⟩
      · rcases le_or_gt t b with h'' | h''
        · exact Or.inr (Or.inl ⟨h'.le, h''⟩)
        · exact Or.inr (Or.inr ⟨h''.le, ht.2⟩)
    have hcover : satoTateMeasure.real (Icc (a - e) (b + e))
        ≤ satoTateMeasure.real (Icc (a - e) a) + (satoTateMeasure.real (Icc a b)
          + satoTateMeasure.real (Icc b (b + e))) := by
      calc satoTateMeasure.real (Icc (a - e) (b + e))
          ≤ satoTateMeasure.real (Icc (a - e) a ∪ (Icc a b ∪ Icc b (b + e))) :=
            measureReal_mono hsub (by simp [measure_ne_top])
        _ ≤ satoTateMeasure.real (Icc (a - e) a)
              + satoTateMeasure.real (Icc a b ∪ Icc b (b + e)) := measureReal_union_le _ _
        _ ≤ satoTateMeasure.real (Icc (a - e) a)
              + (satoTateMeasure.real (Icc a b) + satoTateMeasure.real (Icc b (b + e))) := by
            gcongr
            exact measureReal_union_le _ _
    have h1 : satoTateMeasure.real (Icc (a - e) a) ≤ δ / 8 := by
      have := satoTateMeasure_real_Icc_le (x := a - e) (y := a) (by linarith)
      rw [← hsmall]; simpa using this
    have h2 : satoTateMeasure.real (Icc b (b + e)) ≤ δ / 8 := by
      have := satoTateMeasure_real_Icc_le (x := b) (y := b + e) (by linarith)
      rw [← hsmall]; simpa using this
    have hLeq : satoTateMeasure.real (Icc a b) = L := rfl
    rw [hLeq] at hcover
    linarith
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.1 hglim) (δ / 4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.1 hhlim) (δ / 4) (by positivity)
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have h1 := hN₁ N (le_of_max_le_left hN)
  have h2 := hN₂ N (le_of_max_le_right hN)
  rw [Real.dist_eq, abs_lt] at h1 h2
  have hlow : avg (S N) θ g
      ≤ (((S N).filter (fun p => θ p ∈ Icc a b)).card : ℝ) / (S N).card := by
    rw [← avg_indicator]
    exact avg_mono (fun t => trapezoid_le_indicator he t)
  have hhigh : (((S N).filter (fun p => θ p ∈ Icc a b)).card : ℝ) / (S N).card
      ≤ avg (S N) θ h := by
    rw [← avg_indicator]
    exact avg_mono (fun t => indicator_le_trapezoid he (by linarith) (by linarith) t)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end Equidistribution

end Math2

import Mathlib

/-!
# The Sato–Tate measure

The Sato–Tate measure is the probability measure `(2/π) sin²θ dθ` on the interval `[0, π]`.
-/

open MeasureTheory Real Set

namespace Math2

/-- The Sato–Tate density `(2/π) sin²(t)`. -/
noncomputable def satoTateDensity (t : ℝ) : ℝ := 2 / π * Real.sin t ^ 2

/-- The Sato–Tate measure: the measure with density `(2/π) sin²(t)` on `[0, π]`. -/
noncomputable def satoTateMeasure : Measure ℝ :=
  (volume.restrict (Icc 0 π)).withDensity (fun t => ENNReal.ofReal (satoTateDensity t))

lemma continuous_satoTateDensity : Continuous satoTateDensity := by
  unfold satoTateDensity; fun_prop

lemma measurable_satoTateDensity : Measurable satoTateDensity :=
  continuous_satoTateDensity.measurable

lemma satoTateDensity_nonneg (t : ℝ) : 0 ≤ satoTateDensity t := by
  have : (0:ℝ) < π := Real.pi_pos
  unfold satoTateDensity
  positivity

lemma satoTateDensity_le (t : ℝ) : satoTateDensity t ≤ 2 / π := by
  have h1 : Real.sin t ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_sin t, Real.sin_le_one t]
  have h2 : (0:ℝ) < 2 / π := by
    have := Real.pi_pos; positivity
  unfold satoTateDensity
  nlinarith

lemma integrableOn_satoTateDensity (s : Set ℝ) (hs : s ⊆ Icc 0 π) :
    IntegrableOn satoTateDensity s volume :=
  (continuous_satoTateDensity.integrableOn_Icc (a := 0) (b := π)).mono_set hs

/-- The Sato–Tate measure is dominated by a multiple of Lebesgue measure on `[0, π]`. -/
lemma satoTateMeasure_le_smul :
    satoTateMeasure ≤ ENNReal.ofReal (2 / π) • (volume.restrict (Icc 0 π)) := by
  rw [satoTateMeasure, ← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall fun t =>
    ENNReal.ofReal_le_ofReal (satoTateDensity_le t))

lemma satoTateMeasure_le_volume (s : Set ℝ) :
    satoTateMeasure s ≤ ENNReal.ofReal (2 / π) * volume s := by
  calc satoTateMeasure s ≤ (ENNReal.ofReal (2 / π) • (volume.restrict (Icc 0 π))) s :=
        satoTateMeasure_le_smul s
    _ = ENNReal.ofReal (2 / π) * (volume.restrict (Icc 0 π)) s := by simp [Measure.smul_apply]
    _ ≤ ENNReal.ofReal (2 / π) * volume s :=
        mul_le_mul_right (Measure.restrict_le_self s) _

lemma satoTateMeasure_apply {s : Set ℝ} (hs : MeasurableSet s) :
    satoTateMeasure s = ENNReal.ofReal (∫ t in s ∩ Icc 0 π, satoTateDensity t) := by
  rw [satoTateMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrableOn_satoTateDensity _ inter_subset_right)
    (Filter.Eventually.of_forall satoTateDensity_nonneg)).symm

/-- The Sato–Tate measure of a subinterval of `[0, π]`, as a real number. -/
lemma satoTateMeasure_Icc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ π) :
    satoTateMeasure (Icc a b) = ENNReal.ofReal (∫ t in a..b, satoTateDensity t) := by
  rcases le_or_gt a b with hab | hab
  · have hsub : Icc a b ∩ Icc 0 π = Icc a b :=
      inter_eq_self_of_subset_left (Icc_subset_Icc ha hb)
    rw [satoTateMeasure_apply measurableSet_Icc, hsub,
      intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  · rw [Icc_eq_empty (not_le.mpr hab), measure_empty]
    symm
    rw [ENNReal.ofReal_eq_zero, intervalIntegral.integral_symm, neg_nonpos,
      intervalIntegral.integral_of_le hab.le]
    exact setIntegral_nonneg measurableSet_Ioc fun t _ => satoTateDensity_nonneg t

lemma satoTateMeasure_Icc_toReal {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π) :
    (satoTateMeasure (Icc a b)).toReal = ∫ t in a..b, satoTateDensity t := by
  rw [satoTateMeasure_Icc ha hb, ENNReal.toReal_ofReal]
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_nonneg measurableSet_Ioc fun t _ => satoTateDensity_nonneg t

lemma satoTateMeasure_compl_Icc : satoTateMeasure (Icc 0 π)ᶜ = 0 := by
  rw [satoTateMeasure_apply measurableSet_Icc.compl, compl_inter_self]
  simp

lemma satoTateMeasure_ae_mem_Icc : ∀ᵐ t ∂satoTateMeasure, t ∈ Icc 0 π := by
  rw [ae_iff]
  convert satoTateMeasure_compl_Icc using 2

lemma integral_satoTateDensity_zero_pi : ∫ t in (0:ℝ)..π, satoTateDensity t = 1 := by
  have hpi := Real.pi_pos
  unfold satoTateDensity
  rw [intervalIntegral.integral_const_mul, integral_sin_sq]
  norm_num [Real.sin_pi, Real.cos_pi]

instance satoTateMeasure_isProbabilityMeasure : IsProbabilityMeasure satoTateMeasure := by
  constructor
  have h : satoTateMeasure univ = satoTateMeasure (Icc 0 π) := by
    rw [satoTateMeasure_apply MeasurableSet.univ, satoTateMeasure_apply measurableSet_Icc,
      univ_inter, inter_self]
  rw [h, satoTateMeasure_Icc le_rfl le_rfl, integral_satoTateDensity_zero_pi, ENNReal.ofReal_one]

lemma integrable_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f satoTateMeasure := by
  have h2 : (0:ℝ) < 2 / π := by have := Real.pi_pos; positivity
  refine Integrable.mono_measure ?_ satoTateMeasure_le_smul
  rw [integrable_smul_measure (by simp [ENNReal.ofReal_eq_zero, not_le, h2])
    (by simp)]
  exact (hf.integrableOn_Icc (a := 0) (b := π))

/-- Integration against the Sato–Tate measure, as an interval integral. -/
lemma integral_satoTateMeasure (f : ℝ → ℝ) :
    ∫ t, f t ∂satoTateMeasure = ∫ t in (0:ℝ)..π, f t * satoTateDensity t := by
  rw [satoTateMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_satoTateDensity.ennreal_ofReal)
    (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top)]
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [smul_eq_mul, ENNReal.toReal_ofReal (satoTateDensity_nonneg t), mul_comm]

end Math2

import RequestProject.SatoTate.Measure

/-!
# Chebyshev polynomials and the Sato–Tate measure

The polynomials `U n` (Chebyshev of the second kind) form an orthonormal family for the
Sato–Tate measure; here we only need that `U n` integrates to `0` for `n ≥ 1` (and to `1`
for `n = 0`), which is the classical Weyl criterion input for Sato–Tate.
-/

open MeasureTheory Real Set Polynomial

namespace Math2

/-- `t ↦ P.eval (cos t)` is continuous. -/
lemma continuous_eval_cos (P : Polynomial ℝ) :
    Continuous fun t : ℝ => P.eval (Real.cos t) :=
  P.continuous_aeval.comp Real.continuous_cos

lemma integral_cos_nat_mul_zero_pi {k : ℕ} (hk : 1 ≤ k) :
    ∫ t in (0:ℝ)..π, Real.cos (k * t) = 0 := by
  have hk0 : (k:ℝ) ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hk0]
  simp [Real.sin_nat_mul_pi]

/-- The Chebyshev polynomials of the second kind have mean zero for the Sato–Tate measure
(the mean of `U 0 = 1` being `1`). -/
lemma integral_chebyshevU_satoTateMeasure (n : ℕ) (hn : 1 ≤ n) :
    ∫ t, (Polynomial.Chebyshev.U ℝ n).eval (Real.cos t) ∂satoTateMeasure = 0 := by
  rw [integral_satoTateMeasure]
  have key : ∀ t : ℝ, (Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (Real.cos t) * satoTateDensity t
      = 1 / π * Real.cos (n * t) - 1 / π * Real.cos ((n + 2 : ℕ) * t) := by
    intro t
    have h := Polynomial.Chebyshev.U_real_cos t (n:ℤ)
    have hcc : Real.cos ((n:ℝ) * t) - Real.cos (((n:ℝ) + 2) * t)
        = 2 * Real.sin (((n:ℝ) + 1) * t) * Real.sin t := by
      rw [Real.cos_sub_cos]
      have h1 : ((n:ℝ) * t + ((n:ℝ) + 2) * t) / 2 = ((n:ℝ) + 1) * t := by ring
      have h2 : ((n:ℝ) * t - ((n:ℝ) + 2) * t) / 2 = -t := by ring
      rw [h1, h2, Real.sin_neg]
      ring
    have hcast : ((n + 2 : ℕ) : ℝ) = (n:ℝ) + 2 := by push_cast; ring
    rw [hcast]
    unfold satoTateDensity
    have hrw : (Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (Real.cos t) * (2 / π * Real.sin t ^ 2)
        = 2 / π * ((Polynomial.Chebyshev.U ℝ (n:ℤ)).eval (Real.cos t) * Real.sin t)
          * Real.sin t := by
      ring
    rw [hrw, h]
    push_cast
    linear_combination (-1 / π) * hcc
  simp only [key]
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_cos_nat_mul_zero_pi hn, integral_cos_nat_mul_zero_pi (by omega : 1 ≤ n + 2)]
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- Every real polynomial is a linear combination of Chebyshev polynomials of the second kind:
this is packaged as an induction principle. -/
lemma chebyshevU_span_induction {motive : Polynomial ℝ → Prop}
    (hU : ∀ n : ℕ, motive (Polynomial.Chebyshev.U ℝ n))
    (hsmul : ∀ (c : ℝ) (P : Polynomial ℝ), motive P → motive (Polynomial.C c * P))
    (hadd : ∀ P Q : Polynomial ℝ, motive P → motive Q → motive (P + Q))
    (P : Polynomial ℝ) : motive P := by
  suffices H : ∀ d : ℕ, ∀ P : Polynomial ℝ, P.natDegree ≤ d → motive P from H P.natDegree P le_rfl
  intro d
  induction d with
  | zero =>
    intro P hP
    have hPC : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hP
    have h1 : Polynomial.C (P.coeff 0) = Polynomial.C (P.coeff 0) * Polynomial.Chebyshev.U ℝ 0 := by
      simp [Polynomial.Chebyshev.U_zero]
    rw [hPC, h1]
    exact hsmul _ _ (hU 0)
  | succ d ih =>
    intro P hP
    set c : ℝ := P.coeff (d + 1) with hc
    set Q : Polynomial ℝ :=
      P - Polynomial.C (c / 2 ^ (d + 1)) * Polynomial.Chebyshev.U ℝ ((d + 1 : ℕ) : ℤ) with hQdef
    have hUdeg : (Polynomial.Chebyshev.U ℝ ((d + 1 : ℕ) : ℤ)).natDegree = d + 1 :=
      Polynomial.Chebyshev.natDegree_U_natCast ℝ (d + 1)
    have hUcoeff : (Polynomial.Chebyshev.U ℝ ((d + 1 : ℕ) : ℤ)).coeff (d + 1) = 2 ^ (d + 1) := by
      have := Polynomial.Chebyshev.leadingCoeff_U_natCast (R := ℝ) (d + 1)
      rwa [Polynomial.leadingCoeff, hUdeg] at this
    have hQ : Q.natDegree ≤ d := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hQdef, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hN) with heq | hlt
      · rw [← heq, hUcoeff, ← hc]
        field_simp
        ring
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP hlt),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hUdeg]; exact hlt)]
        ring
    have hsplit : P = Q + Polynomial.C (c / 2 ^ (d + 1)) * Polynomial.Chebyshev.U ℝ ((d + 1 : ℕ) : ℤ) := by
      rw [hQdef]; ring
    rw [hsplit]
    exact hadd _ _ (ih Q hQ) (hsmul _ _ (hU (d + 1)))

end Math2

