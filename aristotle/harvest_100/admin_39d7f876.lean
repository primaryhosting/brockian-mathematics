import Mathlib

/-!
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
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

set_option grind.warning false

open MeasureTheory

namespace Frontier

/-- Auxiliary: a differentiable function is continuous. -/
private lemma continuous_of_hasDerivAt {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x) :
    Continuous u :=
  continuous_iff_continuousAt.2 fun x => (hu x).continuousAt

/-- Auxiliary: from a point outside a large ball the function vanishes; we pick a base point
to the left of any given `x`. -/
private lemma exists_base_point {u : ℝ → ℝ} (hsupp : HasCompactSupport u) (x : ℝ) :
    ∃ a : ℝ, a ≤ x ∧ u a = 0 := by
  obtain ⟨R, hR0, hR⟩ := hsupp.exists_pos_le_norm
  refine ⟨min x (-R), min_le_left _ _, hR _ ?_⟩
  have h : min x (-R) ≤ -R := min_le_right _ _
  have hneg : min x (-R) < 0 := lt_of_le_of_lt h (by linarith)
  rw [Real.norm_eq_abs, abs_of_neg hneg]
  linarith

/-- **Gagliardo–Nirenberg–Sobolev, one-dimensional base case (`L¹` form).**
If `u : ℝ → ℝ` is differentiable with derivative `u'` and has compact support, and `u'` is
integrable, then `u` is bounded by the `L¹` norm of its derivative. -/
theorem abs_le_integral_abs_deriv {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hint : Integrable u') (hsupp : HasCompactSupport u) (x : ℝ) :
    |u x| ≤ ∫ y, |u' y| := by
  obtain ⟨a, hax, hua⟩ := exists_base_point hsupp x
  have key : ∫ y in a..x, u' y = u x - u a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hu y)
      hint.intervalIntegrable
  rw [hua, sub_zero] at key
  calc |u x| = |∫ y in a..x, u' y| := by rw [key]
    _ ≤ ∫ y in a..x, |u' y| := intervalIntegral.abs_integral_le_integral_abs hax
    _ ≤ ∫ y, |u' y| := by
        rw [intervalIntegral.integral_of_le hax]
        exact setIntegral_le_integral hint.abs
          (Filter.Eventually.of_forall fun y => abs_nonneg _)

/-- **The Gagliardo–Nirenberg interpolation inequality (one-dimensional base case).**
For a compactly supported continuously differentiable function `u : ℝ → ℝ` with derivative `u'`,
one has the pointwise interpolation bound
`u x ^ 2 ≤ 2 ‖u‖_{L²} ‖u'‖_{L²}`,
i.e. `‖u‖_∞ ≤ √2 · ‖u‖_{L²}^{1/2} · ‖u'‖_{L²}^{1/2}`. -/
theorem nirenberg_gagliardo {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') (hsupp : HasCompactSupport u) (x : ℝ) :
    u x ^ 2 ≤ 2 * Real.sqrt (∫ y, u y ^ 2) * Real.sqrt (∫ y, u' y ^ 2) := by
  have hcu : Continuous u := continuous_of_hasDerivAt hu
  have hsupp' : HasCompactSupport u' := by
    have h1 : HasCompactSupport (deriv u) := hsupp.deriv
    have h2 : deriv u = u' := funext fun y => (hu y).deriv
    rwa [h2] at h1
  obtain ⟨a, hax, hua⟩ := exists_base_point hsupp x
  -- the product `2 u u'` is continuous with compact support, hence integrable
  have hcont : Continuous fun y => 2 * u y * u' y := by fun_prop
  have hcs : HasCompactSupport fun y => 2 * u y * u' y := by
    apply HasCompactSupport.mul_right
    exact HasCompactSupport.mul_left (f := fun _ => (2 : ℝ)) hsupp
  have hInt : Integrable fun y => 2 * u y * u' y :=
    hcont.integrable_of_hasCompactSupport hcs
  -- fundamental theorem of calculus applied to `u ^ 2`
  have hd : ∀ y ∈ Set.uIcc a x, HasDerivAt (fun z => u z ^ 2) (2 * u y * u' y) y := by
    intro y _
    have h := (hu y).pow 2
    simpa [pow_one, mul_comm, mul_assoc, mul_left_comm] using h
  have key : ∫ y in a..x, (2 * u y * u' y) = u x ^ 2 - u a ^ 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hInt.intervalIntegrable
  rw [hua] at key
  have h1 : u x ^ 2 ≤ ∫ y in a..x, |2 * u y * u' y| := by
    calc u x ^ 2 = ∫ y in a..x, (2 * u y * u' y) := by rw [key]; ring
      _ ≤ |∫ y in a..x, (2 * u y * u' y)| := le_abs_self _
      _ ≤ _ := intervalIntegral.abs_integral_le_integral_abs hax
  have h2 : (∫ y in a..x, |2 * u y * u' y|) ≤ ∫ y, |2 * u y * u' y| := by
    rw [intervalIntegral.integral_of_le hax]
    exact setIntegral_le_integral hInt.abs (Filter.Eventually.of_forall fun y => abs_nonneg _)
  have h3 : (∫ y, |2 * u y * u' y|) = 2 * ∫ y, |u y| * |u' y| := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [abs_mul]
    ring
  -- Cauchy–Schwarz
  have hmu : MemLp (fun y => |u y|) 2 volume :=
    (hcu.memLp_of_hasCompactSupport (μ := volume) hsupp).abs
  have hmu' : MemLp (fun y => |u' y|) 2 volume :=
    (hu'.memLp_of_hasCompactSupport (μ := volume) hsupp').abs
  have hCS : (∫ y, |u y| * |u' y|)
      ≤ (∫ y, |u y| ^ (2:ℝ)) ^ ((1:ℝ)/2) * (∫ y, |u' y| ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
    have := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume) (p := 2) (q := 2) Real.HolderConjugate.two_two
      (f := fun y => |u y|) (g := fun y => |u' y|)
      (Filter.Eventually.of_forall fun y => abs_nonneg _)
      (Filter.Eventually.of_forall fun y => abs_nonneg _)
      (by simpa using hmu) (by simpa using hmu')
    simpa using this
  have habs2 : ∀ v : ℝ → ℝ, (∫ y, |v y| ^ (2:ℝ)) = ∫ y, v y ^ 2 := by
    intro v
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [sq_abs]
  rw [habs2 u, habs2 u'] at hCS
  have hsq : ∀ v : ℝ → ℝ, Real.sqrt (∫ y, v y ^ 2) = (∫ y, v y ^ 2) ^ ((1:ℝ)/2) := by
    intro v; rw [Real.sqrt_eq_rpow]
  rw [hsq u, hsq u']
  calc u x ^ 2 ≤ ∫ y in a..x, |2 * u y * u' y| := h1
    _ ≤ ∫ y, |2 * u y * u' y| := h2
    _ = 2 * ∫ y, |u y| * |u' y| := h3
    _ ≤ 2 * ((∫ y, u y ^ 2) ^ ((1:ℝ)/2) * (∫ y, u' y ^ 2) ^ ((1:ℝ)/2)) := by
        exact mul_le_mul_of_nonneg_left hCS (by norm_num)
    _ = 2 * (∫ y, u y ^ 2) ^ ((1:ℝ)/2) * (∫ y, u' y ^ 2) ^ ((1:ℝ)/2) := by ring

end Frontier

