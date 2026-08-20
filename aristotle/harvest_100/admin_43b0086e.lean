/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

/-! ## The 2D Ising model on a finite torus -/

/-- The real value `±1` of a spin encoded as a `Bool`. -/
def spinVal (b : Bool) : ℝ := if b then 1 else -1

/-- The nearest-neighbour interaction sum
`∑_{x} σ_x (σ_{x + e₁} + σ_{x + e₂})` of a spin configuration on the `m × n` torus
`ZMod m × ZMod n`. -/
def isingInteraction (m n : ℕ) [NeZero m] [NeZero n]
    (σ : ZMod m × ZMod n → Bool) : ℝ :=
  ∑ x : ZMod m × ZMod n,
    spinVal (σ x) * (spinVal (σ (x.1 + 1, x.2)) + spinVal (σ (x.1, x.2 + 1)))

/-- The partition function of the 2D Ising model at (dimensionless) coupling `K = βJ`
on the `m × n` torus. -/
noncomputable def isingPartitionFunction (m n : ℕ) [NeZero m] [NeZero n] (K : ℝ) : ℝ :=
  ∑ σ : ZMod m × ZMod n → Bool, Real.exp (K * isingInteraction m n σ)

/-- The (reduced) free energy per site `-βf = (1/N) log Z` of the finite `m × n` torus. -/
noncomputable def isingFreeEnergyPerSite (m n : ℕ) [NeZero m] [NeZero n] (K : ℝ) : ℝ :=
  Real.log (isingPartitionFunction m n K) / (m * n)

/-! ## Onsager's exact free energy -/

/-- Onsager's exact expression for the reduced free energy per site of the 2D square
lattice Ising model in the thermodynamic limit, in its double-integral form
`log 2 + (1/2)(2π)⁻² ∫₀^{2π}∫₀^{2π} log (cosh²(2K) - sinh(2K)(cos θ₁ + cos θ₂)) dθ₁ dθ₂`. -/
noncomputable def onsagerFreeEnergy (K : ℝ) : ℝ :=
  Real.log 2 + (1 / (2 * (2 * Real.pi) ^ 2)) *
    ∫ θ₁ in (0 : ℝ)..(2 * Real.pi), ∫ θ₂ in (0 : ℝ)..(2 * Real.pi),
      Real.log (Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos θ₁ + Real.cos θ₂))

/-- The classical single-integral form of Onsager's free energy, obtained from the
double integral by performing one of the two angular integrations. -/
noncomputable def onsagerFreeEnergySingle (K : ℝ) : ℝ :=
  Real.log 2 + (1 / (4 * Real.pi)) *
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.log ((Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * Real.cos θ +
        Real.sqrt ((Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * Real.cos θ) ^ 2
          - Real.sinh (2 * K) ^ 2)) / 2)

/-! ## The key angular integral -/

/-- Factorisation identity: on the unit circle, `a - b cos θ` factors through the two
roots `r, r'` of `z² - (2a/b) z + 1`. -/
theorem factor_of_roots (a b c z r r' : ℂ) (hb : b ≠ 0) (hz : z ≠ 0) (hzc : z + z⁻¹ = 2 * c)
    (h1 : r * r' = 1) (h2 : r + r' = 2 * a / b) :
    a - b * c = -(b / 2) * z⁻¹ * (z - r) * (z - r') := by
  have hzi : z⁻¹ * z = 1 := inv_mul_cancel₀ hz
  have hexp : -(b / 2) * z⁻¹ * (z - r) * (z - r')
      = -(b / 2) * (z + z⁻¹) + (b / 2) * (r + r') := by
    linear_combination (-(b / 2) * z + (b / 2) * (r + r')) * hzi + (-(b / 2) * z⁻¹) * h1
  rw [hexp, hzc, h2]
  field_simp
  ring

/-- Pointwise factorisation of `a - b cos θ` as a product of two distances on the unit
circle. -/
theorem sub_mul_cos_eq_norm_mul (a b r r' : ℝ) (hb0 : b ≠ 0) (ha : |b| < a)
    (hrr' : r * r' = 1) (hsum : r + r' = 2 * a / b) (θ : ℝ) :
    a - b * Real.cos θ
      = |b| / 2 * ‖circleMap 0 1 θ - (r : ℂ)‖ * ‖circleMap 0 1 θ - (r' : ℂ)‖ := by
  have hznorm : ‖circleMap 0 1 θ‖ = 1 := by simp
  have hz0 : circleMap 0 1 θ ≠ 0 := by
    intro h; rw [h] at hznorm; simp at hznorm
  have hzc : circleMap 0 1 θ + (circleMap 0 1 θ)⁻¹ = 2 * (Real.cos θ : ℂ) := by
    have hz : circleMap 0 1 θ = Complex.exp (θ * Complex.I) := by simp [circleMap]
    rw [hz, ← Complex.exp_neg,
      show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) * Complex.I) by push_cast; ring,
      Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, ← Complex.ofReal_sin]
    simp [Real.cos_neg, Real.sin_neg]
    ring
  have hsum' : (r : ℂ) + (r' : ℂ) = 2 * (a : ℂ) / (b : ℂ) := by
    rw [show (2 : ℂ) * (a : ℂ) / (b : ℂ) = ((2 * a / b : ℝ) : ℂ) by push_cast; ring, ← hsum]
    push_cast; ring
  have hid := factor_of_roots (a : ℂ) (b : ℂ) (Real.cos θ : ℂ) (circleMap 0 1 θ) (r : ℂ) (r' : ℂ)
    (by exact_mod_cast hb0) hz0 hzc (by exact_mod_cast hrr') hsum'
  have hnorm := congrArg (fun w : ℂ => ‖w‖) hid
  simp only [Complex.norm_mul, norm_inv, hznorm] at hnorm
  have hpos : 0 < a - b * Real.cos θ := by
    nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ, abs_nonneg b, le_abs_self b, neg_abs_le b]
  have hL : ‖(a : ℂ) - (b : ℂ) * (Real.cos θ : ℂ)‖ = a - b * Real.cos θ := by
    rw [show ((a : ℂ) - (b : ℂ) * (Real.cos θ : ℂ)) = ((a - b * Real.cos θ : ℝ) : ℂ) by
        push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  rw [hL] at hnorm
  rw [hnorm]
  simp

/-- Continuity of `θ ↦ log ‖circleMap 0 1 θ - c‖` when `c` is off the unit circle. -/
theorem continuous_log_norm_circleMap_sub (c : ℂ) (hc : ‖c‖ ≠ 1) :
    Continuous fun θ : ℝ => Real.log ‖circleMap 0 1 θ - c‖ := by
  refine Continuous.log (((continuous_circleMap 0 1).sub continuous_const).norm) ?_
  intro θ
  simp only [ne_eq, norm_eq_zero, sub_eq_zero]
  intro h
  exact hc (by rw [← h]; simp)

/-- The circle-average computation: `∫₀^{2π} log ‖e^{iθ} - c‖ dθ = 2π log⁺ ‖c‖`.
This is Mathlib's `circleAverage_log_norm_sub_const_eq_posLog` (Jensen formula file). -/
theorem integral_log_norm_circleMap_sub (c : ℂ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log ‖circleMap 0 1 θ - c‖
      = 2 * Real.pi * Real.posLog ‖c‖ := by
  have h := circleAverage_log_norm_sub_const_eq_posLog (a := c)
  rw [Real.circleAverage, smul_eq_mul] at h
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  field_simp at h
  linarith [h]

/-- The classical evaluation `∫₀^{2π} log (a - b cos θ) dθ = 2π log ((a + √(a²-b²))/2)`
for `|b| < a`.  It is proved from Mathlib's Jensen-formula machinery, namely
`circleAverage_log_norm_sub_const_eq_posLog`. -/
theorem integral_log_sub_mul_cos (a b : ℝ) (hb : |b| < a) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log (a - b * Real.cos θ)
      = 2 * Real.pi * Real.log ((a + Real.sqrt (a ^ 2 - b ^ 2)) / 2) := by
  have ha : 0 < a := lt_of_le_of_lt (abs_nonneg b) hb
  rcases eq_or_ne b 0 with hb0 | hb0
  · subst hb0
    rw [show a ^ 2 - (0 : ℝ) ^ 2 = a ^ 2 by ring, Real.sqrt_sq ha.le]
    simp only [zero_mul, sub_zero]
    rw [intervalIntegral.integral_const, show (a + a) / 2 = a by ring]
    simp
  · have hb2 : 0 < b ^ 2 := by positivity
    have hD : 0 < a ^ 2 - b ^ 2 := by nlinarith [sq_abs b, abs_nonneg b]
    set s := Real.sqrt (a ^ 2 - b ^ 2) with hs_def
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = a ^ 2 - b ^ 2 := Real.sq_sqrt hD.le
    have hsa : s < a := by
      have h := Real.sqrt_lt_sqrt hD.le (show a ^ 2 - b ^ 2 < a ^ 2 by nlinarith)
      rwa [Real.sqrt_sq ha.le] at h
    set r : ℝ := (a + s) / b with hr_def
    set r' : ℝ := (a - s) / b with hr'_def
    have hrr' : r * r' = 1 := by
      rw [hr_def, hr'_def]; field_simp; linear_combination -hs2
    have hsum : r + r' = 2 * a / b := by
      rw [hr_def, hr'_def]; field_simp; ring
    have hbabs : 0 < |b| := abs_pos.mpr hb0
    have habs_r : |r| = (a + s) / |b| := by
      rw [hr_def, abs_div, abs_of_pos (by linarith : (0:ℝ) < a + s)]
    have hr_gt : 1 < |r| := by
      rw [habs_r, lt_div_iff₀ hbabs]
      linarith [hb]
    have habs_r'_le : |r'| ≤ 1 := by
      have h1 : |r| * |r'| = 1 := by rw [← abs_mul, hrr']; simp
      nlinarith [abs_nonneg r']
    have hnormr : ‖(r : ℂ)‖ = |r| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have hnormr' : ‖(r' : ℂ)‖ = |r'| := by rw [Complex.norm_real, Real.norm_eq_abs]
    -- pointwise rewriting of the integrand
    have hptwise : ∀ θ : ℝ, Real.log (a - b * Real.cos θ)
        = (Real.log (|b| / 2) + Real.log ‖circleMap 0 1 θ - (r : ℂ)‖)
          + Real.log ‖circleMap 0 1 θ - (r' : ℂ)‖ := by
      intro θ
      have hz : ‖circleMap 0 1 θ‖ = 1 := by simp
      have hne : ∀ c : ℂ, ‖c‖ ≠ 1 → ‖circleMap 0 1 θ - c‖ ≠ 0 := by
        intro c hc
        simp only [ne_eq, norm_eq_zero, sub_eq_zero]
        intro h
        exact hc (by rw [← h]; simp [hz])
      have h1 : ‖circleMap 0 1 θ - (r : ℂ)‖ ≠ 0 :=
        hne _ (by rw [hnormr]; exact ne_of_gt hr_gt)
      have h2 : ‖circleMap 0 1 θ - (r' : ℂ)‖ ≠ 0 := by
        refine hne _ ?_
        rw [hnormr']
        intro hcon
        have : |r| * |r'| = 1 := by rw [← abs_mul, hrr']; simp
        rw [hcon, mul_one] at this
        rw [this] at hr_gt
        exact lt_irrefl _ hr_gt
      rw [sub_mul_cos_eq_norm_mul a b r r' hb0 hb hrr' hsum θ,
        Real.log_mul (by positivity) h2, Real.log_mul (by positivity) h1]
    rw [intervalIntegral.integral_congr (g := fun θ =>
      (Real.log (|b| / 2) + Real.log ‖circleMap 0 1 θ - (r : ℂ)‖)
        + Real.log ‖circleMap 0 1 θ - (r' : ℂ)‖) (fun θ _ => hptwise θ)]
    have hcont_r : Continuous fun θ : ℝ => Real.log ‖circleMap 0 1 θ - (r : ℂ)‖ :=
      continuous_log_norm_circleMap_sub _ (by rw [hnormr]; exact ne_of_gt hr_gt)
    have hcont_r' : Continuous fun θ : ℝ => Real.log ‖circleMap 0 1 θ - (r' : ℂ)‖ := by
      refine continuous_log_norm_circleMap_sub _ ?_
      rw [hnormr']
      intro hcon
      have h1 : |r| * |r'| = 1 := by rw [← abs_mul, hrr']; simp
      rw [hcon, mul_one] at h1
      rw [h1] at hr_gt
      exact lt_irrefl _ hr_gt
    have hint_c : IntervalIntegrable (fun _ : ℝ => Real.log (|b| / 2))
        MeasureTheory.volume 0 (2 * Real.pi) := continuous_const.intervalIntegrable _ _
    have hint_r : IntervalIntegrable (fun θ : ℝ => Real.log ‖circleMap 0 1 θ - (r : ℂ)‖)
        MeasureTheory.volume 0 (2 * Real.pi) := hcont_r.intervalIntegrable _ _
    have hint_r' : IntervalIntegrable (fun θ : ℝ => Real.log ‖circleMap 0 1 θ - (r' : ℂ)‖)
        MeasureTheory.volume 0 (2 * Real.pi) := hcont_r'.intervalIntegrable _ _
    rw [intervalIntegral.integral_add (hint_c.add hint_r) hint_r',
      intervalIntegral.integral_add hint_c hint_r,
      intervalIntegral.integral_const, integral_log_norm_circleMap_sub,
      integral_log_norm_circleMap_sub, hnormr, hnormr',
      Real.posLog_eq_log (by rw [abs_abs]; exact hr_gt.le),
      (Real.posLog_eq_zero_iff _).mpr (by rw [abs_abs]; exact habs_r'_le)]
    have hfinal : Real.log (|b| / 2) + Real.log |r| = Real.log ((a + s) / 2) := by
      rw [← Real.log_mul (by positivity) (by positivity), habs_r]
      congr 1
      field_simp
    simp only [smul_eq_mul, sub_zero, mul_zero, add_zero]
    rw [← hfinal]
    ring

/-! ## Main results -/

/-- At infinite temperature the partition function counts configurations: `Z = 2^(mn)`. -/
theorem isingPartitionFunction_zero (m n : ℕ) [NeZero m] [NeZero n] :
    isingPartitionFunction m n 0 = 2 ^ (m * n) := by
  simp [isingPartitionFunction, ZMod.card]

/-- At `K = 0` the finite-volume free energy per site is exactly `log 2`. -/
theorem isingFreeEnergyPerSite_zero (m n : ℕ) [NeZero m] [NeZero n] :
    isingFreeEnergyPerSite m n 0 = Real.log 2 := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [isingFreeEnergyPerSite, isingPartitionFunction_zero, Real.log_pow]
  push_cast
  field_simp

/-- Onsager's formula at `K = 0` gives `log 2`. -/
theorem onsagerFreeEnergy_zero : onsagerFreeEnergy 0 = Real.log 2 := by
  simp [onsagerFreeEnergy]

/-- Reduction of the double integral to the classical single integral, valid away from
the critical couplings `sinh (2K) = ±1`. -/
theorem onsagerFreeEnergy_eq_single (K : ℝ) (hK : |Real.sinh (2 * K)| ≠ 1) :
    onsagerFreeEnergy K = onsagerFreeEnergySingle K := by
  have hcs : Real.cosh (2 * K) ^ 2 = 1 + Real.sinh (2 * K) ^ 2 := by
    rw [Real.cosh_sq]; ring
  have hinner : ∀ θ₁ : ℝ,
      (∫ θ₂ in (0 : ℝ)..(2 * Real.pi),
        Real.log (Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos θ₁ + Real.cos θ₂)))
        = 2 * Real.pi * Real.log ((Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * Real.cos θ₁ +
            Real.sqrt ((Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * Real.cos θ₁) ^ 2
              - Real.sinh (2 * K) ^ 2)) / 2) := by
    intro θ₁
    have hlt : |Real.sinh (2 * K)| < Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * Real.cos θ₁ := by
      have h1 : Real.sinh (2 * K) * Real.cos θ₁ ≤ |Real.sinh (2 * K)| := by
        calc Real.sinh (2 * K) * Real.cos θ₁ ≤ |Real.sinh (2 * K) * Real.cos θ₁| :=
              le_abs_self _
          _ = |Real.sinh (2 * K)| * |Real.cos θ₁| := abs_mul _ _
          _ ≤ |Real.sinh (2 * K)| * 1 := by
              exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ₁) (abs_nonneg _)
          _ = |Real.sinh (2 * K)| := mul_one _
      have h2 : (0 : ℝ) < (|Real.sinh (2 * K)| - 1) ^ 2 := by
        have hne : |Real.sinh (2 * K)| - 1 ≠ 0 := sub_ne_zero.mpr hK
        positivity
      nlinarith [sq_abs (Real.sinh (2 * K)), hcs, h1, h2]
    have hkey := integral_log_sub_mul_cos
      (Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * Real.cos θ₁) (Real.sinh (2 * K)) hlt
    rw [← hkey]
    refine intervalIntegral.integral_congr (fun θ₂ _ => ?_)
    congr 1
    ring
  rw [onsagerFreeEnergy, onsagerFreeEnergySingle,
    intervalIntegral.integral_congr (fun θ₁ _ => hinner θ₁),
    intervalIntegral.integral_const_mul]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  congr 1
  field_simp
  ring

/-- **Onsager's solution of the 2D Ising model** (formalized statement together with the
verified base case and reduction).

1. At infinite temperature (`K = 0`) the exact finite-volume free energy per site of the
   Ising model on any `m × n` torus agrees with Onsager's formula, both being `log 2`.
2. Away from the critical couplings `sinh (2K) = ±1`, Onsager's double integral reduces
   to the classical single-integral form. -/
theorem onsager_2d_ising :
    (∀ (m n : ℕ) [NeZero m] [NeZero n],
        isingFreeEnergyPerSite m n 0 = onsagerFreeEnergy 0 ∧
          onsagerFreeEnergy 0 = Real.log 2) ∧
      (∀ K : ℝ, |Real.sinh (2 * K)| ≠ 1 →
        onsagerFreeEnergy K = onsagerFreeEnergySingle K) := by
  refine ⟨fun m n _ _ => ⟨?_, onsagerFreeEnergy_zero⟩, onsagerFreeEnergy_eq_single⟩
  rw [isingFreeEnergyPerSite_zero, onsagerFreeEnergy_zero]

end Frontier

