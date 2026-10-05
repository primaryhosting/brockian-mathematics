/-
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory

set_option autoImplicit false

namespace Frontier

/--
**Gagliardo–Nirenberg (base case, `n = 1`, `p = 1`).**

If `u : ℝ → ℝ` is everywhere differentiable with derivative `u'`, `u'` is integrable, and `u`
has compact support, then

`‖u‖_{L^∞} ≤ (1/2) * ‖u'‖_{L^1}`,

pointwise: `|u x| ≤ (1/2) * ∫ t, |u' t|` for every `x`.

This is the one-dimensional endpoint case of the Gagliardo–Nirenberg–Sobolev inequality: it is
obtained by writing `u x` both as `∫_{-S}^{x} u'` and as `-∫_{x}^{S} u'` (where `[-S, S]` contains
the support of `u`), and adding the two resulting bounds.  The constant `1/2` is sharp.
-/
theorem nirenberg_gagliardo
    {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Integrable u')
    (hsupp : HasCompactSupport u) (x : ℝ) :
    |u x| ≤ (1 / 2) * ∫ t, |u' t| := by
  have habs : Integrable (fun t => |u' t|) := hu'.abs
  obtain ⟨R, hR⟩ := hsupp.isBounded.subset_closedBall (0 : ℝ)
  set S := |R| + 1 with hSdef
  have hSpos : (0 : ℝ) < S := by positivity
  -- `u` vanishes outside the interval `[-S, S]`
  have hzero : ∀ y : ℝ, S ≤ |y| → u y = 0 := by
    intro y hy
    have hmem : y ∉ tsupport u := by
      intro hmem
      have h := hR hmem
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
      rw [hSdef] at hy
      linarith [le_abs_self R]
    have hns : y ∉ Function.support u := fun hs => hmem (subset_tsupport u hs)
    simpa [Function.mem_support] using hns
  -- the integral of `|u'|` over any interval is at most its integral over `ℝ`
  have htot : ∀ a b : ℝ, a ≤ b → (∫ t in a..b, |u' t|) ≤ ∫ t, |u' t| := by
    intro a b hab
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_le_integral habs (Filter.Eventually.of_forall fun t => abs_nonneg _)
  have hnonneg : (0 : ℝ) ≤ ∫ t, |u' t| := integral_nonneg fun t => abs_nonneg _
  by_cases hx : x ∈ Set.Icc (-S) S
  · obtain ⟨hx1, hx2⟩ := hx
    have h1 : (∫ t in (-S)..x, u' t) = u x - u (-S) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hu y) hu'.intervalIntegrable
    have h2 : (∫ t in x..S, u' t) = u S - u x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hu y) hu'.intervalIntegrable
    have e1 : u (-S) = 0 := hzero _ (by rw [abs_neg, abs_of_pos hSpos])
    have e2 : u S = 0 := hzero _ (by rw [abs_of_pos hSpos])
    rw [e1, sub_zero] at h1
    rw [e2, zero_sub] at h2
    have b1 : |u x| ≤ ∫ t in (-S)..x, |u' t| := by
      rw [← h1]
      exact intervalIntegral.abs_integral_le_integral_abs (by linarith)
    have b2 : |u x| ≤ ∫ t in x..S, |u' t| := by
      have h := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
        (f := u') (a := x) (b := S)
        (by linarith)
      rw [h2, abs_neg] at h
      exact h
    have hadd : (∫ t in (-S)..x, |u' t|) + (∫ t in x..S, |u' t|) = ∫ t in (-S)..S, |u' t| :=
      intervalIntegral.integral_add_adjacent_intervals
        habs.intervalIntegrable habs.intervalIntegrable
    have hle := htot (-S) S (by linarith)
    linarith
  · have hu0 : u x = 0 := by
      apply hzero
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    rw [hu0, abs_zero]
    linarith

/--
**Gagliardo–Nirenberg, `L^1` interpolation form.**

Under the same hypotheses, `‖u‖_{L^∞}^2 ≤ ∫ |u| |u'|`.  This is obtained by applying the base
case to `u^2`, whose derivative is `2 u u'`.
-/
theorem nirenberg_gagliardo_sq
    {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Integrable u')
    (hsupp : HasCompactSupport u) (x : ℝ) :
    |u x| ^ 2 ≤ ∫ t, |u t| * |u' t| := by
  have hcont : Continuous u := continuous_iff_continuousAt.mpr fun y => (hu y).continuousAt
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hcont
  have hmul : Integrable (fun t => 2 * u t * u' t) := by
    have h : Integrable (fun t => (2 * u t) * u' t) :=
      hu'.bdd_mul (c := 2 * C) (by fun_prop)
        (Filter.Eventually.of_forall fun t => by
          have h1 : |u t| ≤ C := by simpa using hC t
          rw [Real.norm_eq_abs, abs_mul, abs_two]
          linarith)
    simpa [mul_assoc] using h
  have hd : ∀ y, HasDerivAt (fun z => u z * u z) (2 * u y * u' y) y := by
    intro y
    have h := (hu y).mul (hu y)
    convert h using 1
    ring
  have hsupp2 : HasCompactSupport (fun z => u z * u z) := hsupp.mul_right
  have key := nirenberg_gagliardo hd hmul hsupp2 x
  have heq : (fun t => |2 * u t * u' t|) = fun t => 2 * (|u t| * |u' t|) := by
    funext t
    rw [abs_mul, abs_mul, abs_two]
    ring
  rw [heq, integral_const_mul] at key
  calc |u x| ^ 2 = |u x * u x| := by rw [abs_mul]; ring
    _ ≤ 1 / 2 * (2 * ∫ t, |u t| * |u' t|) := key
    _ = ∫ t, |u t| * |u' t| := by ring

/-- Cauchy–Schwarz inequality for Bochner integrals of real functions. -/
theorem integral_mul_le_sqrt_mul_sqrt {f g : ℝ → ℝ} (hf : Integrable (fun x => f x ^ 2))
    (hg : Integrable (fun x => g x ^ 2)) (hfg : Integrable (fun x => f x * g x)) :
    (∫ x, f x * g x) ≤ Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, g x ^ 2) := by
  set A := ∫ x, f x ^ 2 with hA
  set B := ∫ x, g x ^ 2 with hB
  set C := ∫ x, f x * g x with hC
  have hA0 : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun x => sq_nonneg _
  -- the quadratic `t ↦ ∫ (f - t g)^2` is nonnegative
  have key : ∀ t : ℝ, 0 ≤ A - 2 * t * C + t ^ 2 * B := by
    intro t
    have hrw : (fun x => (f x - t * g x) ^ 2)
        = fun x => (f x ^ 2 - 2 * t * (f x * g x)) + t ^ 2 * g x ^ 2 := by
      funext x; ring
    have h0 : 0 ≤ ∫ x, (f x - t * g x) ^ 2 := integral_nonneg fun x => sq_nonneg _
    rw [hrw] at h0
    have e1 : (∫ x, (f x ^ 2 - 2 * t * (f x * g x)) + t ^ 2 * g x ^ 2)
        = (∫ x, (f x ^ 2 - 2 * t * (f x * g x))) + ∫ x, t ^ 2 * g x ^ 2 :=
      integral_add (hf.sub (hfg.const_mul (2 * t))) (hg.const_mul (t ^ 2))
    have e2 : (∫ x, (f x ^ 2 - 2 * t * (f x * g x))) = A - ∫ x, 2 * t * (f x * g x) :=
      integral_sub hf (hfg.const_mul (2 * t))
    have e3 : (∫ x, 2 * t * (f x * g x)) = 2 * t * C := integral_const_mul _ _
    have e4 : (∫ x, t ^ 2 * g x ^ 2) = t ^ 2 * B := integral_const_mul _ _
    rw [e1, e2, e3, e4] at h0
    linarith
  rcases eq_or_lt_of_le hB0 with hB0' | hBpos
  · -- degenerate case `∫ g^2 = 0`, which forces `∫ f g = 0`
    have hC0 : C = 0 := by
      by_contra hne
      have h := key ((A + 1) / (2 * C))
      rw [← hB0'] at h
      have hx : 2 * ((A + 1) / (2 * C)) * C = A + 1 := by field_simp
      rw [hx] at h
      simp at h
      linarith
    rw [hC0, ← hB0']
    simp
  · set D := C ^ 2 / B with hD
    have hx : 2 * (C / B) * C = 2 * D := by rw [hD]; field_simp
    have hy : (C / B) ^ 2 * B = D := by rw [hD]; field_simp
    have h := key (C / B)
    rw [hx, hy] at h
    have h2 : D ≤ A := by linarith
    have hsq : C ^ 2 ≤ A * B := by
      have hCD : C ^ 2 = D * B := by rw [hD]; field_simp
      rw [hCD]
      exact mul_le_mul_of_nonneg_right h2 hB0
    calc C ≤ |C| := le_abs_self C
      _ = Real.sqrt (C ^ 2) := (Real.sqrt_sq_eq_abs C).symm
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA0 B

/--
**Gagliardo–Nirenberg, `L^2` interpolation form (Ladyzhenskaya's inequality in dimension 1).**

If `u` is everywhere differentiable with integrable, square integrable derivative `u'`, and `u`
has compact support, then

`‖u‖_{L^∞}^2 ≤ ‖u‖_{L^2} * ‖u'‖_{L^2}`.
-/
theorem nirenberg_gagliardo_L2
    {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Integrable u')
    (hu'sq : Integrable fun t => u' t ^ 2)
    (hsupp : HasCompactSupport u) (x : ℝ) :
    |u x| ^ 2 ≤ Real.sqrt (∫ t, u t ^ 2) * Real.sqrt (∫ t, u' t ^ 2) := by
  have hcont : Continuous u := continuous_iff_continuousAt.mpr fun y => (hu y).continuousAt
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hcont
  have hsuppsq : HasCompactSupport fun t => |u t| ^ 2 := by
    apply hsupp.comp_left (g := fun y : ℝ => |y| ^ 2)
    simp
  have husq : Integrable fun t => |u t| ^ 2 :=
    (by fun_prop : Continuous fun t => |u t| ^ 2).integrable_of_hasCompactSupport hsuppsq
  have hu'sq' : Integrable fun t => |u' t| ^ 2 := by simpa [sq_abs] using hu'sq
  have hmul : Integrable fun t => |u t| * |u' t| :=
    hu'.abs.bdd_mul (c := C) (by fun_prop)
      (Filter.Eventually.of_forall fun t => by simpa using hC t)
  have hcs := integral_mul_le_sqrt_mul_sqrt husq hu'sq' hmul
  simp only [sq_abs] at hcs
  exact le_trans (nirenberg_gagliardo_sq hu hu' hsupp x) hcs

end Frontier

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

