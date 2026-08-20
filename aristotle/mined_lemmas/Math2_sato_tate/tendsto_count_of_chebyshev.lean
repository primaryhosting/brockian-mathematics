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
