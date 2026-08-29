/-
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the mandated
-- header above is written as an ordinary block comment; its text is unchanged.)

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

namespace Phys

/-! ## Definitions -/

/-- The **Unruh temperature** `T = ℏ a / (2 π c k_B)` associated with proper acceleration `a`. -/
noncomputable def unruhTemp (hbar a c kB : ℝ) : ℝ := hbar * a / (2 * Real.pi * c * kB)

/-- Time coordinate `t(τ)` of the worldline of an observer with constant proper acceleration `a`,
parametrized by proper time `τ` (Rindler / hyperbolic motion in 1+1 Minkowski space). -/
noncomputable def rindlerT (a c τ : ℝ) : ℝ := (c / a) * Real.sinh (a * τ / c)

/-- Space coordinate `x(τ)` of the uniformly accelerated worldline. -/
noncomputable def rindlerX (a c τ : ℝ) : ℝ := (c ^ 2 / a) * Real.cosh (a * τ / c)

/-- Minkowski interval squared, `(c Δt)² - (Δx)²`, between two points of the accelerated
worldline (signature `(+,-)`). -/
noncomputable def rindlerIntervalSq (a c τ₁ τ₂ : ℝ) : ℝ :=
  (c * (rindlerT a c τ₁ - rindlerT a c τ₂)) ^ 2 - (rindlerX a c τ₁ - rindlerX a c τ₂) ^ 2

/-- The analytic continuation of the worldline interval to complex proper-time separation.
Vacuum two-point (Wightman) functions along the worldline are functions of this quantity, so
its periodicity in imaginary time is exactly the KMS thermality condition. -/
noncomputable def rindlerIntervalSqC (a c : ℝ) (Δ : ℂ) : ℂ :=
  4 * ((c : ℂ) ^ 2 / (a : ℂ)) ^ 2 * (Complex.sinh ((a : ℂ) * Δ / (2 * (c : ℂ)))) ^ 2

/-- Bose–Einstein (Planck) mean occupation number at temperature `T` for a mode of angular
frequency `ω`. -/
noncomputable def bosePlanck (hbar kB T ω : ℝ) : ℝ := 1 / (Real.exp (hbar * ω / (kB * T)) - 1)

/-! ## Kinematics of the uniformly accelerated worldline -/

private lemma hasDerivAt_lin (a c : ℝ) (τ : ℝ) :
    HasDerivAt (fun s : ℝ => a * s / c) (a / c) τ := by
  simpa [mul_comm, mul_div_assoc] using ((hasDerivAt_id τ).const_mul a).div_const c

lemma hasDerivAt_rindlerT (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    HasDerivAt (rindlerT a c) (Real.cosh (a * τ / c)) τ := by
  have h3 := ((Real.hasDerivAt_sinh (a * τ / c)).comp τ (hasDerivAt_lin a c τ)).const_mul (c / a)
  have heq : c / a * (Real.cosh (a * τ / c) * (a / c)) = Real.cosh (a * τ / c) := by
    field_simp
  exact h3.congr_deriv heq

lemma hasDerivAt_rindlerX (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    HasDerivAt (rindlerX a c) (c * Real.sinh (a * τ / c)) τ := by
  have h3 :=
    ((Real.hasDerivAt_cosh (a * τ / c)).comp τ (hasDerivAt_lin a c τ)).const_mul (c ^ 2 / a)
  have heq : c ^ 2 / a * (Real.sinh (a * τ / c) * (a / c)) = c * Real.sinh (a * τ / c) := by
    field_simp
  exact h3.congr_deriv heq

lemma deriv_rindlerT (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    deriv (rindlerT a c) = fun τ => Real.cosh (a * τ / c) :=
  funext fun τ => (hasDerivAt_rindlerT a c ha hc τ).deriv

lemma deriv_rindlerX (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    deriv (rindlerX a c) = fun τ => c * Real.sinh (a * τ / c) :=
  funext fun τ => (hasDerivAt_rindlerX a c ha hc τ).deriv

lemma deriv2_rindlerT (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    deriv (deriv (rindlerT a c)) = fun τ => (a / c) * Real.sinh (a * τ / c) := by
  rw [deriv_rindlerT a c ha hc]
  funext τ
  have h2 := (Real.hasDerivAt_cosh (a * τ / c)).comp τ (hasDerivAt_lin a c τ)
  exact (h2.congr_deriv (by ring)).deriv

lemma deriv2_rindlerX (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    deriv (deriv (rindlerX a c)) = fun τ => a * Real.cosh (a * τ / c) := by
  rw [deriv_rindlerX a c ha hc]
  funext τ
  have h2 := ((Real.hasDerivAt_sinh (a * τ / c)).comp τ (hasDerivAt_lin a c τ)).const_mul c
  have hx : c * (Real.cosh (a * τ / c) * (a / c)) = a * Real.cosh (a * τ / c) := by
    field_simp
  exact (h2.congr_deriv hx).deriv

/-- The worldline is parametrized by proper time: its four-velocity has constant norm `c`. -/
theorem rindler_unit_fourvelocity (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    (c * deriv (rindlerT a c) τ) ^ 2 - (deriv (rindlerX a c) τ) ^ 2 = c ^ 2 := by
  rw [deriv_rindlerT a c ha hc, deriv_rindlerX a c ha hc]
  nlinarith [Real.cosh_sq_sub_sinh_sq (a * τ / c)]

/-- The worldline has constant proper acceleration of magnitude `|a|`. -/
theorem rindler_proper_acceleration (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    (deriv (deriv (rindlerX a c)) τ) ^ 2 - (c * deriv (deriv (rindlerT a c)) τ) ^ 2 = a ^ 2 := by
  rw [deriv2_rindlerT a c ha hc, deriv2_rindlerX a c ha hc]
  have h : c * ((a / c) * Real.sinh (a * τ / c)) = a * Real.sinh (a * τ / c) := by
    field_simp
  rw [h]
  nlinarith [Real.cosh_sq_sub_sinh_sq (a * τ / c)]

/-! ## The two-point interval along the worldline -/

lemma cosh_sub_one (x : ℝ) : Real.cosh x - 1 = 2 * Real.sinh (x / 2) ^ 2 := by
  have h : Real.cosh x
      = Real.cosh (x / 2) * Real.cosh (x / 2) + Real.sinh (x / 2) * Real.sinh (x / 2) := by
    rw [← Real.cosh_add]; ring_nf
  nlinarith [Real.cosh_sq_sub_sinh_sq (x / 2)]

/-- The Minkowski interval between two points of the uniformly accelerated worldline depends
only on the proper-time difference, through `sinh²(a Δτ / 2c)`. -/
theorem rindler_intervalSq_eq (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (τ₁ τ₂ : ℝ) :
    rindlerIntervalSq a c τ₁ τ₂
      = 4 * (c ^ 2 / a) ^ 2 * Real.sinh (a * (τ₁ - τ₂) / (2 * c)) ^ 2 := by
  have hkey : Real.cosh (a * τ₁ / c - a * τ₂ / c) - 1
      = 2 * Real.sinh (a * (τ₁ - τ₂) / (2 * c)) ^ 2 := by
    have h := cosh_sub_one (a * τ₁ / c - a * τ₂ / c)
    have harg : (a * τ₁ / c - a * τ₂ / c) / 2 = a * (τ₁ - τ₂) / (2 * c) := by
      field_simp
    rw [harg] at h
    exact h
  rw [Real.cosh_sub] at hkey
  have h1 := Real.cosh_sq_sub_sinh_sq (a * τ₁ / c)
  have h2 := Real.cosh_sq_sub_sinh_sq (a * τ₂ / c)
  simp only [rindlerIntervalSq, rindlerT, rindlerX]
  have hexp : (c * (c / a * Real.sinh (a * τ₁ / c) - c / a * Real.sinh (a * τ₂ / c))) ^ 2
      - (c ^ 2 / a * Real.cosh (a * τ₁ / c) - c ^ 2 / a * Real.cosh (a * τ₂ / c)) ^ 2
      = (c ^ 2 / a) ^ 2 *
        ((Real.sinh (a * τ₁ / c) - Real.sinh (a * τ₂ / c)) ^ 2
          - (Real.cosh (a * τ₁ / c) - Real.cosh (a * τ₂ / c)) ^ 2) := by
    field_simp
  rw [hexp]
  nlinarith [h1, h2, hkey]

/-- The complexified interval restricts to the real interval on real proper-time separations. -/
theorem rindlerIntervalSqC_ofReal (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (τ₁ τ₂ : ℝ) :
    rindlerIntervalSqC a c ((τ₁ - τ₂ : ℝ) : ℂ) = ((rindlerIntervalSq a c τ₁ τ₂ : ℝ) : ℂ) := by
  rw [rindler_intervalSq_eq a c ha hc]
  simp only [rindlerIntervalSqC]
  have harg : ((a : ℂ)) * ((τ₁ - τ₂ : ℝ) : ℂ) / (2 * (c : ℂ))
      = ((a * (τ₁ - τ₂) / (2 * c) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, ← Complex.ofReal_sinh]
  push_cast
  ring

/-! ## KMS periodicity in imaginary proper time -/

/-- The complexified worldline correlation variable is periodic in imaginary proper time with
period `2πc/a`. This is the KMS condition at inverse temperature `β = 2πc/a`. -/
theorem rindlerIntervalSqC_kms_period (a c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (Δ : ℂ) :
    rindlerIntervalSqC a c (Δ + Complex.I * ((2 * Real.pi * c / a : ℝ) : ℂ))
      = rindlerIntervalSqC a c Δ := by
  simp only [rindlerIntervalSqC]
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have harg : (a : ℂ) * (Δ + Complex.I * ((2 * Real.pi * c / a : ℝ) : ℂ)) / (2 * (c : ℂ))
      = (a : ℂ) * Δ / (2 * (c : ℂ)) + (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [harg, Complex.sinh_add]
  have h1 : Complex.sinh ((Real.pi : ℂ) * Complex.I) = 0 := by
    rw [Complex.sinh_mul_I]
    simp
  have h2 : Complex.cosh ((Real.pi : ℂ) * Complex.I) = -1 := by
    rw [Complex.cosh_mul_I]
    simp
  rw [h1, h2]
  ring

/-- Minimality: `2πc/a` is the smallest positive imaginary period, so the KMS temperature is
uniquely determined. -/
theorem rindlerIntervalSqC_kms_period_minimal (a c : ℝ) (ha : 0 < a) (hc : 0 < c) (b : ℝ)
    (hb : 0 < b)
    (hper : ∀ Δ : ℂ, rindlerIntervalSqC a c (Δ + Complex.I * (b : ℂ))
      = rindlerIntervalSqC a c Δ) :
    2 * Real.pi * c / a ≤ b := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have h0 := hper 0
  simp only [rindlerIntervalSqC, zero_add, mul_zero, zero_div, Complex.sinh_zero] at h0
  have hcoef : (4 : ℂ) * ((c : ℂ) ^ 2 / (a : ℂ)) ^ 2 ≠ 0 := by
    have hne : ((c : ℂ) ^ 2 / (a : ℂ)) ≠ 0 := div_ne_zero (pow_ne_zero 2 hc') ha'
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hne)
  have hs : Complex.sinh ((a : ℂ) * (Complex.I * (b : ℂ)) / (2 * (c : ℂ))) ^ 2 = 0 := by
    have h0' := h0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h0'
    exact (mul_eq_zero.mp h0').resolve_left hcoef
  have hs0 : Complex.sinh ((a : ℂ) * (Complex.I * (b : ℂ)) / (2 * (c : ℂ))) = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hs
  have harg : (a : ℂ) * (Complex.I * (b : ℂ)) / (2 * (c : ℂ))
      = ((a * b / (2 * c) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [harg, Complex.sinh_mul_I] at hs0
  have hsin : Real.sin (a * b / (2 * c)) = 0 := by
    have hcs : Complex.sin (((a * b / (2 * c) : ℝ) : ℂ)) = 0 := by
      rcases mul_eq_zero.mp hs0 with h | h
      · exact h
      · exact absurd h Complex.I_ne_zero
    rw [← Complex.ofReal_sin] at hcs
    exact_mod_cast hcs
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
  have hpos : 0 < a * b / (2 * c) := by positivity
  have hn1 : (1 : ℤ) ≤ n := by
    by_contra hcon
    push_neg at hcon
    have hle : (n : ℝ) ≤ 0 := by exact_mod_cast Int.lt_add_one_iff.mp hcon
    nlinarith [Real.pi_pos]
  have hpi_le : Real.pi ≤ a * b / (2 * c) := by
    rw [← hn]
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    nlinarith [Real.pi_pos]
  have hcc : (0 : ℝ) < 2 * c := by linarith
  rw [le_div_iff₀ hcc] at hpi_le
  rw [div_le_iff₀ ha]
  linarith

/-! ## Thermality: the inverse temperature is `ℏ/(k_B T_U)` -/

/-- The KMS imaginary period `2πc/a` equals `ℏ / (k_B T)` exactly for `T` the Unruh
temperature. -/
theorem unruh_beta (hbar a c kB : ℝ) (hbar0 : hbar ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0) (hk : kB ≠ 0) :
    hbar / (kB * unruhTemp hbar a c kB) = 2 * Real.pi * c / a := by
  have hpi := Real.pi_ne_zero
  simp only [unruhTemp]
  field_simp

/-- Detailed balance: the Boltzmann factor generated by the KMS period `2πc/a` is exactly the
thermal factor at the Unruh temperature. -/
theorem unruh_detailed_balance (hbar a c kB : ℝ) (hbar0 : hbar ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (hk : kB ≠ 0) (ω : ℝ) :
    Real.exp (-(2 * Real.pi * c * ω / a))
      = Real.exp (-(hbar * ω / (kB * unruhTemp hbar a c kB))) := by
  congr 1
  have h := unruh_beta hbar a c kB hbar0 ha hc hk
  have hsplit : hbar * ω / (kB * unruhTemp hbar a c kB)
      = (hbar / (kB * unruhTemp hbar a c kB)) * ω := by ring
  rw [hsplit, h]
  ring

/-- A mode whose emission/absorption rates satisfy detailed balance at temperature `T`
has the Planck (Bose–Einstein) mean occupation number at that temperature. -/
theorem planck_of_detailed_balance (hbar kB T ω : ℝ) (hne : Real.exp (hbar * ω / (kB * T)) ≠ 1)
    (n : ℝ) (hn : 1 + n ≠ 0) (hbal : n / (1 + n) = Real.exp (-(hbar * ω / (kB * T)))) :
    n = bosePlanck hbar kB T ω := by
  set E := hbar * ω / (kB * T) with hE
  have hexp : Real.exp E ≠ 0 := Real.exp_ne_zero E
  rw [Real.exp_neg, inv_eq_one_div, div_eq_div_iff hn hexp] at hbal
  have h2 : n * (Real.exp E - 1) = 1 := by linear_combination hbal
  have hd : Real.exp E - 1 ≠ 0 := sub_ne_zero_of_ne hne
  rw [bosePlanck, ← hE, eq_div_iff hd]
  exact h2

/-! ## Main theorem -/

/--
**The Unruh effect.**

An observer moving with constant proper acceleration `a` through the Minkowski vacuum
perceives a thermal bath at the *Unruh temperature*

`T = ℏ a / (2 π c k_B)`.

The statement below packages the derivation:

1. `rindlerT`, `rindlerX` describe a worldline parametrized by proper time
   (four-velocity of constant norm `c`) with constant proper acceleration `a`;
2. the Minkowski interval between two points of that worldline depends only on the
   proper-time separation `Δτ`, and equals `(4c⁴/a²) sinh²(aΔτ/2c)`;
3. this expression, analytically continued in `Δτ`, is periodic in imaginary proper time
   with period `ℏ/(k_B T)`, and `ℏ/(k_B T)` is the *smallest* positive such period —
   this is the KMS condition, which identifies `T` as the temperature of the state;
4. the resulting Boltzmann factor is `exp(-2πcω/a) = exp(-ℏω/(k_B T))`, and detailed balance
   with this factor forces the Planck spectrum `n(ω) = 1/(exp(ℏω/(k_B T)) - 1)`;
5. and the temperature so determined is `T = ℏ a / (2 π c k_B)`.
-/
theorem unruh_effect {hbar a c kB : ℝ} (hbar0 : 0 < hbar) (ha : 0 < a) (hc : 0 < c)
    (hk : 0 < kB) :
    -- (0) the Unruh temperature is positive and equals ℏ a / (2 π c k_B)
    0 < unruhTemp hbar a c kB ∧
    unruhTemp hbar a c kB = hbar * a / (2 * Real.pi * c * kB) ∧
    -- (1) kinematics: proper-time parametrization and constant proper acceleration `a`
    (∀ τ : ℝ, (c * deriv (rindlerT a c) τ) ^ 2 - (deriv (rindlerX a c) τ) ^ 2 = c ^ 2) ∧
    (∀ τ : ℝ,
      (deriv (deriv (rindlerX a c)) τ) ^ 2 - (c * deriv (deriv (rindlerT a c)) τ) ^ 2 = a ^ 2) ∧
    -- (2) the worldline two-point interval
    (∀ τ₁ τ₂ : ℝ, rindlerIntervalSq a c τ₁ τ₂
        = 4 * (c ^ 2 / a) ^ 2 * Real.sinh (a * (τ₁ - τ₂) / (2 * c)) ^ 2) ∧
    (∀ τ₁ τ₂ : ℝ, rindlerIntervalSqC a c ((τ₁ - τ₂ : ℝ) : ℂ)
        = ((rindlerIntervalSq a c τ₁ τ₂ : ℝ) : ℂ)) ∧
    -- (3) KMS periodicity in imaginary proper time with minimal period ℏ/(k_B T)
    (∀ Δ : ℂ, rindlerIntervalSqC a c
        (Δ + Complex.I * ((hbar / (kB * unruhTemp hbar a c kB) : ℝ) : ℂ))
        = rindlerIntervalSqC a c Δ) ∧
    (∀ b : ℝ, 0 < b →
      (∀ Δ : ℂ, rindlerIntervalSqC a c (Δ + Complex.I * (b : ℂ)) = rindlerIntervalSqC a c Δ) →
      hbar / (kB * unruhTemp hbar a c kB) ≤ b) ∧
    -- (4) thermality: Boltzmann factor and Planck spectrum at the Unruh temperature
    (∀ ω : ℝ, Real.exp (-(2 * Real.pi * c * ω / a))
        = Real.exp (-(hbar * ω / (kB * unruhTemp hbar a c kB)))) ∧
    (∀ ω : ℝ, 0 < ω → ∀ n : ℝ, 1 + n ≠ 0 →
      n / (1 + n) = Real.exp (-(hbar * ω / (kB * unruhTemp hbar a c kB))) →
      n = bosePlanck hbar kB (unruhTemp hbar a c kB) ω) := by
  have hpi := Real.pi_pos
  have hT : 0 < unruhTemp hbar a c kB := by
    simp only [unruhTemp]
    positivity
  have hbeta : hbar / (kB * unruhTemp hbar a c kB) = 2 * Real.pi * c / a :=
    unruh_beta hbar a c kB hbar0.ne' ha.ne' hc.ne' hk.ne'
  refine ⟨hT, rfl, fun τ => rindler_unit_fourvelocity a c ha.ne' hc.ne' τ,
    fun τ => rindler_proper_acceleration a c ha.ne' hc.ne' τ,
    fun τ₁ τ₂ => rindler_intervalSq_eq a c ha.ne' hc.ne' τ₁ τ₂,
    fun τ₁ τ₂ => rindlerIntervalSqC_ofReal a c ha.ne' hc.ne' τ₁ τ₂, ?_, ?_, ?_, ?_⟩
  · intro Δ
    rw [hbeta]
    exact rindlerIntervalSqC_kms_period a c ha.ne' hc.ne' Δ
  · intro b hb hper
    rw [hbeta]
    exact rindlerIntervalSqC_kms_period_minimal a c ha hc b hb hper
  · intro ω
    exact unruh_detailed_balance hbar a c kB hbar0.ne' ha.ne' hc.ne' hk.ne' ω
  · intro ω hω n hn hbal
    refine planck_of_detailed_balance hbar kB (unruhTemp hbar a c kB) ω ?_ n hn hbal
    have hEpos : 0 < hbar * ω / (kB * unruhTemp hbar a c kB) := by positivity
    have hlt := Real.exp_lt_exp.mpr hEpos
    rw [Real.exp_zero] at hlt
    exact hlt.ne'

end Phys

