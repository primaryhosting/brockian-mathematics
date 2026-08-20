/-
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
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

namespace QI

/-!
## Setting

We formalise the mathematical core of Shor's period–finding algorithm.

Fix a modulus `N`, an element `a` of order `r` modulo `N`, and a quantum register of
size `Q`.  Shor's algorithm prepares the uniform superposition
`Q^(-1/2) ∑_{x < Q} |x⟩ |a^x mod N⟩`, measures the second register — obtaining some value
`a^{x₀}` with `x₀ < r`, which collapses the first register to the uniform superposition over
the arithmetic progression `{x < Q : x ≡ x₀ [MOD r]}` — applies the quantum Fourier transform
of order `Q` to the first register and measures it.

The probability of observing the value `y` is therefore

  `prob Q r x₀ y = (m Q)⁻¹ * ‖∑_{j < m} exp(2πi (x₀ + j r) y / Q)‖²`,

where `m = numTerms Q r x₀` is the number of elements of the progression.  This is the
distribution `prob` defined below (`prob_sum_eq_one` verifies that it is a probability
distribution).

The theorems that constitute the correctness of the algorithm are:

* `QI.shor_period` : the measured value `y` lies, with probability at least
  `φ(r) / (6 r)`, in the set of outcomes from which the classical post-processing
  (best rational approximation with bounded denominator) returns the period `r`;
* `QI.shor_period_orderOf` : the same statement for `r = orderOf a`, i.e. for the period of
  the modular exponentiation function `x ↦ a ^ x`;
* `QI.recovers_unique` : that post-processing is well defined, i.e. an outcome `y`
  determines at most one period `r`;
* `QI.collapsed_register` : the set `{x < Q : a ^ x = a ^ x₀}` onto which the first register
  collapses is exactly the progression `{x₀ + j r : j < numTerms Q r x₀}`;
* `QI.prob_sum_eq_one` : `prob` is a probability distribution on the `Q` outcomes.
-/

/-- The number of `x < Q` with `x ≡ x₀ [MOD r]` and `x ≥ x₀`, i.e. `⌈(Q - x₀)/r⌉`. -/
def numTerms (Q r x0 : ℕ) : ℕ := (Q - x0 + r - 1) / r

/-- The amplitude of the outcome `y` after the quantum Fourier transform of order `Q` is
applied to the uniform superposition over `{x₀ + j r : j < numTerms Q r x₀}`. -/
noncomputable def amp (Q r x0 y : ℕ) : ℂ :=
  ((Real.sqrt ((numTerms Q r x0 : ℝ) * Q) : ℝ) : ℂ)⁻¹ *
    ∑ j ∈ Finset.range (numTerms Q r x0),
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((x0 : ℂ) + (j : ℂ) * (r : ℂ)) * (y : ℂ)) / (Q : ℂ))

/-- The probability that Shor's algorithm outputs the value `y`. -/
noncomputable def prob (Q r x0 y : ℕ) : ℝ := ‖amp Q r x0 y‖ ^ 2

/-- `y/Q` is within `1/(2B²)` of the fraction `s/r`, whose denominator is at most `B`:
the classical post-processing step of Shor's algorithm (best rational approximation with
denominator at most `B`) applied to the measurement outcome `y` returns the period `r`. -/
def Recovers (B Q r y : ℕ) : Prop :=
  0 < r ∧ r ≤ B ∧ ∃ s : ℕ, Nat.Coprime r s ∧ |(y : ℝ) / Q - (s : ℝ) / r| < 1 / (2 * (B : ℝ) ^ 2)

/-! ## Trigonometric preliminaries -/

theorem cos_eq_one_sub_two_sin_sq (t : ℝ) : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
  have h := Real.cos_two_mul' (t / 2)
  rw [show 2 * (t / 2) = t by ring] at h
  nlinarith [Real.sin_sq_add_cos_sq (t / 2)]

theorem norm_exp_mul_I_sub_one (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (t / 2)| := by
  have h : ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ^ 2 = (2 * |Real.sin (t / 2)|) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      mul_pow, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq t, cos_eq_one_sub_two_sin_sq t]
  nlinarith [norm_nonneg (Complex.exp ((t : ℂ) * Complex.I) - 1), abs_nonneg (Real.sin (t / 2))]

theorem abs_sin_eq_sin_abs {x : ℝ} (h : |x| ≤ Real.pi) : |Real.sin x| = Real.sin |x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx
      (by rwa [abs_of_nonneg hx] at h))]
  · have hs : Real.sin x ≤ 0 := by
      have h1 : Real.sin (-x) ≥ 0 := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by rwa [abs_of_nonpos hx] at h)
      rw [Real.sin_neg] at h1; linarith
    rw [abs_of_nonpos hs, abs_of_nonpos hx, Real.sin_neg]

/-- On `[0, 17π/32]` one has `sin a ≥ a/2`. -/
theorem half_le_sin {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 17 * Real.pi / 32) : a / 2 ≤ Real.sin a := by
  have hpi1 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi2 : Real.pi < 3.15 := Real.pi_lt_d2
  rcases le_total a (Real.pi / 2) with hc | hc
  · have hms := Real.mul_le_sin h0 hc
    have h4 : a / 2 ≤ 2 / Real.pi * a := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : (0:ℝ) < Real.pi)]
      nlinarith
    linarith
  · have hs : Real.sin a = Real.cos (a - Real.pi / 2) := by
      rw [← Real.cos_pi_div_two_sub, ← Real.cos_neg]
      ring_nf
    have hb : 0 ≤ a - Real.pi / 2 := by linarith
    have hb2 : a - Real.pi / 2 ≤ Real.pi / 32 := by linarith
    have hcos := Real.one_sub_sq_div_two_le_cos (x := a - Real.pi / 2)
    nlinarith

/-- Closed form for the modulus of a geometric sum of unit phases. -/
theorem norm_geom_sum_exp (m : ℕ) (t : ℝ) (ht : Real.sin (t / 2) ≠ 0) :
    ‖∑ j ∈ Finset.range m, Complex.exp ((((j : ℝ) * t : ℝ) : ℂ) * Complex.I)‖ =
      |Real.sin ((m : ℝ) * t / 2)| / |Real.sin (t / 2)| := by
  have hz : ∀ j : ℕ, Complex.exp ((((j : ℝ) * t : ℝ) : ℂ) * Complex.I)
      = (Complex.exp ((t:ℂ) * Complex.I)) ^ j := by
    intro j
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [hz]
  have hne : Complex.exp ((t:ℂ) * Complex.I) - 1 ≠ 0 := by
    intro h0
    apply ht
    have h1 := norm_exp_mul_I_sub_one t
    rw [h0] at h1
    simp at h1
    tauto
  rw [geom_sum_eq (by intro h; apply hne; rw [h]; ring), norm_div, ← Complex.exp_nat_mul]
  have hmt : ((m:ℂ) * ((t:ℂ) * Complex.I)) = (((m:ℝ) * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hmt, norm_exp_mul_I_sub_one, norm_exp_mul_I_sub_one,
    mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]

/-- The key lower bound: as long as the total phase spread `m|t|` is at most `17π/16`,
the geometric sum of `m` unit phases has modulus at least `m/2`. -/
theorem norm_geom_sum_exp_lower (m : ℕ) (t : ℝ) (hm : 0 < m) (ht : (m : ℝ) * |t| ≤ 17 * Real.pi / 16) :
    (m : ℝ) / 2 ≤ ‖∑ j ∈ Finset.range m, Complex.exp ((((j : ℝ) * t : ℝ) : ℂ) * Complex.I)‖ := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  rcases eq_or_ne t 0 with rfl | htne
  · simp
  have habs : (0:ℝ) < |t| := abs_pos.2 htne
  have hlet : |t| ≤ (m:ℝ) * |t| := le_mul_of_one_le_left habs.le hm1
  have hthalf : |t / 2| ≤ 17 * Real.pi / 32 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  have hsin : Real.sin (t/2) ≠ 0 := by
    intro h0
    have h1 : |Real.sin (t/2)| = Real.sin |t/2| := abs_sin_eq_sin_abs (by nlinarith)
    rw [h0] at h1
    simp at h1
    have hpos : 0 < Real.sin |t/2| := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
    rw [← h1] at hpos
    exact lt_irrefl _ hpos
  rw [norm_geom_sum_exp m t hsin]
  have e1 : |Real.sin (t/2)| = Real.sin (|t|/2) := by
    rw [abs_sin_eq_sin_abs (by nlinarith), abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have e2 : |Real.sin ((m:ℝ) * t/2)| = Real.sin ((m:ℝ) * |t|/2) := by
    rw [abs_sin_eq_sin_abs, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_mul,
      abs_of_nonneg (le_of_lt hmR)]
    · rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_mul,
        abs_of_nonneg (le_of_lt hmR)]
      linarith
  rw [e1, e2]
  have hu : 0 < |t|/2 := by positivity
  have hupi : |t|/2 < Real.pi := by linarith
  have hsinu : 0 < Real.sin (|t|/2) := Real.sin_pos_of_pos_of_lt_pi hu hupi
  rw [le_div_iff₀ hsinu]
  have hle : Real.sin (|t|/2) ≤ |t|/2 := Real.sin_le (le_of_lt hu)
  have hhalf := half_le_sin (a := (m:ℝ) * |t|/2) (by positivity) (by linarith)
  nlinarith

/-! ## Elementary facts about `numTerms` -/

theorem numTerms_pos {Q r x0 : ℕ} (hr : 0 < r) (h : x0 < Q) : 0 < numTerms Q r x0 :=
  (Nat.one_le_div_iff hr).2 (by omega)

theorem le_numTerms_mul {Q r x0 : ℕ} (hr : 0 < r) : Q ≤ x0 + numTerms Q r x0 * r := by
  unfold numTerms
  set K := Q - x0 + r - 1 with hK
  have h1 := Nat.div_add_mod K r
  have h2 := Nat.mod_lt K hr
  have h3 : K = Q - x0 + r - 1 := hK
  rw [Nat.mul_comm]
  omega

theorem numTerms_mul_le {Q r x0 : ℕ} (hr : 0 < r) (h : x0 < Q) :
    x0 + numTerms Q r x0 * r ≤ Q + r - 1 := by
  unfold numTerms
  set K := Q - x0 + r - 1 with hK
  have h1 := Nat.div_add_mod K r
  have h2 := Nat.mod_lt K hr
  have h3 : K = Q - x0 + r - 1 := hK
  rw [Nat.mul_comm]
  omega

theorem lt_numTerms_iff {Q r x0 j : ℕ} (hr : 0 < r) (hx0 : x0 < Q) :
    j < numTerms Q r x0 ↔ x0 + j * r < Q := by
  have h1 := le_numTerms_mul (Q := Q) (r := r) (x0 := x0) hr
  have h2 := numTerms_mul_le (Q := Q) (r := r) (x0 := x0) hr hx0
  constructor
  · intro hj
    have hle : j * r ≤ (numTerms Q r x0 - 1) * r := Nat.mul_le_mul_right r (by omega)
    have h3 : (numTerms Q r x0 - 1) * r + r = numTerms Q r x0 * r := by
      have h4 : 1 ≤ numTerms Q r x0 := by omega
      cases' Nat.exists_eq_add_of_le h4 with c hc
      rw [hc]; simp; ring
    omega
  · intro hj
    by_contra hcon
    push_neg at hcon
    have : numTerms Q r x0 * r ≤ j * r := Nat.mul_le_mul_right r hcon
    omega

/-! ## The collapsed register is an arithmetic progression

Measuring the second register of `Q^(-1/2) ∑_{x < Q} |x⟩ |a^x⟩` returns some value `a^{x₀}`
with `x₀ < r = orderOf a`, and collapses the first register to the uniform superposition
over `{x < Q : a^x = a^{x₀}}`.  That set is exactly the arithmetic progression
`{x₀ + j r : j < numTerms Q r x₀}` used in the definition of `amp`. -/

theorem collapsed_register {G : Type*} [LeftCancelMonoid G] (a : G) {r Q x0 : ℕ}
    (hr : orderOf a = r) (h0 : 0 < r) (hx0 : x0 < r) (hQ : x0 < Q) :
    (Finset.range Q).filter (fun x => a ^ x = a ^ x0)
      = (Finset.range (numTerms Q r x0)).image (fun j => x0 + j * r) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hxQ, hax⟩
    rw [pow_eq_pow_iff_modEq, hr] at hax
    have hmod : x % r = x0 := by
      have hm : x % r = x0 % r := hax
      rwa [Nat.mod_eq_of_lt hx0] at hm
    have hdm := Nat.div_add_mod x r
    have hcomm : r * (x / r) = (x / r) * r := Nat.mul_comm _ _
    refine ⟨x / r, ?_, ?_⟩
    · rw [lt_numTerms_iff h0 hQ]
      omega
    · omega
  · rintro ⟨j, hj, rfl⟩
    rw [lt_numTerms_iff h0 hQ] at hj
    refine ⟨hj, ?_⟩
    rw [pow_eq_pow_iff_modEq, hr]
    show (x0 + j * r) % r = x0 % r
    simp [Nat.add_mul_mod_self_right]

theorem card_collapsed_register {G : Type*} [LeftCancelMonoid G] (a : G) {r Q x0 : ℕ}
    (hr : orderOf a = r) (h0 : 0 < r) (hx0 : x0 < r) (hQ : x0 < Q) :
    ((Finset.range Q).filter (fun x => a ^ x = a ^ x0)).card = numTerms Q r x0 := by
  rw [collapsed_register a hr h0 hx0 hQ, Finset.card_image_of_injective _ ?_, Finset.card_range]
  intro u v huv
  simp only at huv
  exact Nat.eq_of_mul_eq_mul_right h0 (by omega : u * r = v * r)

/-! ## The probability of a given outcome -/

theorem prob_eq {Q r x0 y : ℕ} :
    prob Q r x0 y =
      ‖∑ j ∈ Finset.range (numTerms Q r x0),
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (((x0 : ℂ) + (j : ℂ) * (r : ℂ)) * (y : ℂ)) / (Q : ℂ))‖ ^ 2 /
        ((numTerms Q r x0 : ℝ) * Q) := by
  unfold prob amp
  rw [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (by positivity)]
  ring

/-- Reduction of the amplitude sum to a geometric sum of unit phases: only the residue
`d = r y - s Q` of `r y` modulo `Q` matters. -/
theorem norm_amp_sum_eq {Q r x0 y s : ℕ} {d : ℤ} (hQ : 0 < Q)
    (h : (r : ℤ) * y = s * Q + d) :
    ‖∑ j ∈ Finset.range (numTerms Q r x0),
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (((x0 : ℂ) + (j : ℂ) * (r : ℂ)) * (y : ℂ)) / (Q : ℂ))‖ =
      ‖∑ j ∈ Finset.range (numTerms Q r x0),
        Complex.exp ((((j : ℝ) * (2 * Real.pi * d / Q) : ℝ) : ℂ) * Complex.I)‖ := by
  have hQC : (Q : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hC : (r : ℂ) * y = s * Q + d := by exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) h
  have key : ∀ j : ℕ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (((x0 : ℂ) + (j : ℂ) * (r : ℂ)) * (y : ℂ)) / (Q : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x0 : ℂ) * y) / (Q : ℂ)) *
        Complex.exp ((((j : ℝ) * (2 * Real.pi * d / Q) : ℝ) : ℂ) * Complex.I) := by
    intro j
    rw [← Complex.exp_add]
    have hshift : 2 * (Real.pi : ℂ) * Complex.I *
          (((x0 : ℂ) + (j : ℂ) * (r : ℂ)) * (y : ℂ)) / (Q : ℂ)
        = (2 * (Real.pi : ℂ) * Complex.I * ((x0 : ℂ) * y) / (Q : ℂ) +
            (((j : ℝ) * (2 * Real.pi * d / Q) : ℝ) : ℂ) * Complex.I)
          + ((j * s : ℤ) : ℂ) * (2 * (Real.pi:ℂ) * Complex.I) := by
      push_cast
      field_simp
      linear_combination (j:ℂ) * hC
    rw [hshift, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [key, ← Finset.mul_sum, norm_mul, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * ((x0 : ℂ) * y) / (Q : ℂ)).re = 0 := by
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
  rw [hre]
  simp

/-- Main analytic estimate: an outcome `y` whose phase `r y` is within `r/2` of a multiple
of `Q` is observed with probability at least `1/(6r)`. -/
theorem prob_lower_bound {Q r x0 y s : ℕ} {d : ℤ} (hr : 0 < r) (hx0 : x0 < r)
    (hQ : 4 * r ^ 2 ≤ Q) (hd : 2 * |d| ≤ (r : ℤ)) (h : (r : ℤ) * y = s * Q + d) :
    1 / (6 * (r : ℝ)) ≤ prob Q r x0 y := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hr1 : 1 ≤ r := hr
  have hQr : 4 * r ≤ Q := by nlinarith
  have hx0Q : x0 < Q := by omega
  have hQpos : 0 < Q := by omega
  set m := numTerms Q r x0 with hmdef
  have hm : 0 < m := numTerms_pos hr hx0Q
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQpos
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr1
  have hQR2 : (4:ℝ) * (r:ℝ)^2 ≤ Q := by exact_mod_cast hQ
  have hmub : (m:ℝ) * r ≤ (Q:ℝ) + r - 1 := by
    have hnat := numTerms_mul_le (Q := Q) (r := r) (x0 := x0) hr hx0Q
    have h3 : ((x0 + m * r : ℕ) : ℝ) ≤ ((Q + r - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    have h4 : ((Q + r - 1 : ℕ) : ℝ) = (Q:ℝ) + r - 1 := by
      have h5 : 1 ≤ Q + r := by omega
      push_cast [Nat.cast_sub h5]
      ring
    push_cast at h3
    rw [h4] at h3
    linarith [Nat.cast_nonneg (α := ℝ) x0]
  have hmlb : (Q:ℝ) ≤ (r:ℝ) + (m:ℝ) * r := by
    have hnat := le_numTerms_mul (Q := Q) (r := r) (x0 := x0) hr
    have h3 : ((Q:ℕ) : ℝ) ≤ ((x0 + m * r : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at h3
    have hx : (x0:ℝ) ≤ r := by
      have hlt : (x0:ℝ) < r := by exact_mod_cast hx0
      linarith
    linarith
  set t : ℝ := 2 * Real.pi * d / Q with htdef
  have habst : |t| = 2 * Real.pi * |(d:ℝ)| / Q := by
    rw [htdef, abs_div, abs_of_pos hQR, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  have hdR : 2 * |(d:ℝ)| ≤ (r:ℝ) := by
    have hc : ((2 * |d| : ℤ) : ℝ) ≤ ((r:ℤ):ℝ) := by exact_mod_cast hd
    push_cast [Int.cast_abs] at hc
    linarith
  have hkey : (m:ℝ) * |t| ≤ 17 * Real.pi / 16 := by
    rw [habst]
    have h1 : (m:ℝ) * (2 * Real.pi * |(d:ℝ)| / Q) = 2 * Real.pi * ((m:ℝ) * |(d:ℝ)|) / Q := by
      field_simp
    rw [h1, div_le_iff₀ hQR]
    have hmd : (m:ℝ) * |(d:ℝ)| ≤ (m:ℝ) * r / 2 := by
      have hhalf : |(d:ℝ)| ≤ (r:ℝ)/2 := by linarith
      nlinarith
    have hQ2 : (16:ℝ) * ((r:ℝ) - 1) ≤ 4 * (r:ℝ)^2 := by nlinarith [sq_nonneg ((r:ℝ) - 2)]
    nlinarith
  have hgeom := norm_geom_sum_exp_lower m t hm hkey
  rw [prob_eq, norm_amp_sum_eq hQpos h, ← hmdef, ← htdef,
    le_div_iff₀ (by positivity : (0:ℝ) < (m:ℝ) * Q)]
  have hnn : (0:ℝ) ≤ ‖∑ j ∈ Finset.range m, Complex.exp ((((j : ℝ) * t : ℝ) : ℂ) * Complex.I)‖ :=
    norm_nonneg _
  have hsq : ((m:ℝ)/2)^2 ≤
      ‖∑ j ∈ Finset.range m, Complex.exp ((((j : ℝ) * t : ℝ) : ℂ) * Complex.I)‖^2 := by
    nlinarith
  have hQ3 : 3 * (r:ℝ) ≤ Q := by nlinarith
  have hfinal : 1 / (6 * (r:ℝ)) * ((m:ℝ) * Q) ≤ ((m:ℝ)/2)^2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity : (0:ℝ) < 6 * (r:ℝ))]
    nlinarith
  linarith

/-! ## Correctness of the classical post-processing -/

/-- Two fractions with denominators at most `B` that are both within `1/(2B²)` of the same
real number are equal.  Hence the rational approximation step of Shor's algorithm has at
most one answer. -/
theorem approx_unique {B p q p' q' : ℕ} {x : ℝ} (hq : 0 < q) (hqB : q ≤ B) (hq' : 0 < q')
    (hq'B : q' ≤ B) (hpq : Nat.Coprime q p) (hpq' : Nat.Coprime q' p')
    (h : |x - (p : ℝ) / q| < 1 / (2 * (B : ℝ) ^ 2))
    (h' : |x - (p' : ℝ) / q'| < 1 / (2 * (B : ℝ) ^ 2)) : p = p' ∧ q = q' := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hq'R : (0:ℝ) < q' := by exact_mod_cast hq'
  have hBR : (0:ℝ) < B := lt_of_lt_of_le hqR (by exact_mod_cast hqB)
  have hlt : |(p:ℝ)/q - (p':ℝ)/q'| < 1 / (B:ℝ)^2 := by
    have ht : |(p:ℝ)/q - (p':ℝ)/q'| ≤ |x - (p:ℝ)/q| + |x - (p':ℝ)/q'| := by
      have := abs_sub_le ((p:ℝ)/q) x ((p':ℝ)/q')
      rwa [abs_sub_comm ((p:ℝ)/q) x] at this
    have h2 : (1:ℝ)/(2*(B:ℝ)^2) + 1/(2*(B:ℝ)^2) = 1/(B:ℝ)^2 := by field_simp; ring
    linarith
  have hkey : (p:ℝ) * q' = p' * q := by
    by_contra hne
    have hne' : ((p:ℤ) * q' - p' * q) ≠ 0 := by
      intro h0
      apply hne
      have := congrArg (fun z : ℤ => (z:ℝ)) h0
      push_cast at this
      linarith
    have h1 : (1:ℝ) ≤ |(p:ℝ) * q' - (p':ℝ) * q| := by
      have h2 : (1:ℤ) ≤ |(p:ℤ) * q' - p' * q| := Int.one_le_abs (by omega)
      have h3 : ((1:ℤ):ℝ) ≤ ((|(p:ℤ) * q' - p' * q| : ℤ) : ℝ) := by exact_mod_cast h2
      rw [Int.cast_abs] at h3
      push_cast at h3
      simpa using h3
    have hdiff : |(p:ℝ)/q - (p':ℝ)/q'| = |(p:ℝ) * q' - (p':ℝ) * q| / ((q:ℝ) * q') := by
      rw [div_sub_div _ _ (ne_of_gt hqR) (ne_of_gt hq'R), abs_div,
        abs_of_pos (mul_pos hqR hq'R), mul_comm (q:ℝ) (p':ℝ)]
    have hqq : (q:ℝ) * q' ≤ (B:ℝ)^2 := by
      have h1 : (q:ℝ) ≤ B := by exact_mod_cast hqB
      have h2 : (q':ℝ) ≤ B := by exact_mod_cast hq'B
      nlinarith
    rw [hdiff, div_lt_iff₀ (mul_pos hqR hq'R)] at hlt
    have hle : (1:ℝ)/(B:ℝ)^2 * ((q:ℝ)*q') ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      exact hqq
    linarith
  have hnat : p * q' = p' * q := by exact_mod_cast hkey
  have hdvd : q ∣ q' := Nat.Coprime.dvd_of_dvd_mul_left hpq ⟨p', by rw [hnat]; ring⟩
  have hdvd' : q' ∣ q := Nat.Coprime.dvd_of_dvd_mul_left hpq' ⟨p, by rw [← hnat]; ring⟩
  have hqq : q = q' := Nat.dvd_antisymm hdvd hdvd'
  subst hqq
  exact ⟨Nat.eq_of_mul_eq_mul_right hq hnat, rfl⟩

/-- The post-processing is unambiguous: an outcome `y` determines at most one period. -/
theorem recovers_unique {B Q r r' y : ℕ} (h : Recovers B Q r y) (h' : Recovers B Q r' y) :
    r = r' := by
  obtain ⟨hr, hrB, s, hs, hy⟩ := h
  obtain ⟨hr', hr'B, s', hs', hy'⟩ := h'
  exact (approx_unique hr hrB hr' hr'B hs hs' hy hy').2

/-! ## The outcomes that reveal the period -/

/-- The outcome closest to `s Q / r`, i.e. `round (s Q / r)`. -/
def goodOutcome (Q r s : ℕ) : ℕ := (2 * s * Q + r) / (2 * r)

theorem goodOutcome_bounds {Q r s : ℕ} (hr : 0 < r) :
    2 * r * goodOutcome Q r s ≤ 2 * s * Q + r ∧
      2 * s * Q + r < 2 * r * goodOutcome Q r s + 2 * r := by
  unfold goodOutcome
  set K := 2 * s * Q + r with hK
  have h1 := Nat.div_add_mod K (2 * r)
  have h2 := Nat.mod_lt K (show 0 < 2 * r by omega)
  exact ⟨by nlinarith [Nat.zero_le (K % (2 * r))], by nlinarith [Nat.zero_le (K % (2 * r))]⟩

theorem goodOutcome_spec {Q r s : ℕ} (hr : 0 < r) :
    2 * |(r : ℤ) * goodOutcome Q r s - s * Q| ≤ r := by
  obtain ⟨h1, h2⟩ := goodOutcome_bounds (Q := Q) (r := r) (s := s) hr
  have h1' : 2 * (r:ℤ) * goodOutcome Q r s ≤ 2 * s * Q + r := by exact_mod_cast h1
  have h2' : 2 * (s:ℤ) * Q + r < 2 * (r:ℤ) * goodOutcome Q r s + 2 * r := by exact_mod_cast h2
  rcases abs_cases ((r : ℤ) * goodOutcome Q r s - s * Q) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
    linarith

theorem goodOutcome_lt {Q r s : ℕ} (hr : 0 < r) (hs : s < r) (hQ : r < 2 * Q) :
    goodOutcome Q r s < Q := by
  obtain ⟨h1, -⟩ := goodOutcome_bounds (Q := Q) (r := r) (s := s) hr
  have h1' : 2 * (r:ℤ) * goodOutcome Q r s ≤ 2 * s * Q + r := by exact_mod_cast h1
  have hs' : (s:ℤ) ≤ (r:ℤ) - 1 := by
    have : (s:ℤ) < r := by exact_mod_cast hs
    linarith
  have hQ' : (r:ℤ) < 2 * Q := by exact_mod_cast hQ
  have hr' : (0:ℤ) < r := by exact_mod_cast hr
  by_contra hcon
  push_neg at hcon
  have hcon' : (Q:ℤ) ≤ goodOutcome Q r s := by exact_mod_cast hcon
  nlinarith [mul_le_mul_of_nonneg_left hcon' (by positivity : (0:ℤ) ≤ 2 * (r:ℤ)),
    mul_le_mul_of_nonneg_right hs' (by linarith : (0:ℤ) ≤ 2 * (Q:ℤ))]

theorem goodOutcome_injOn {Q r : ℕ} (hr : 0 < r) (hQ : r < Q) {s s' : ℕ}
    (h : goodOutcome Q r s = goodOutcome Q r s') : s = s' := by
  have hs := goodOutcome_spec (Q := Q) (r := r) (s := s) hr
  have hs' := goodOutcome_spec (Q := Q) (r := r) (s := s') hr
  rw [← h] at hs'
  have hQ' : (r:ℤ) < Q := by exact_mod_cast hQ
  have key : ((s:ℤ) - s') * Q =
      ((r : ℤ) * goodOutcome Q r s - s' * Q) - ((r : ℤ) * goodOutcome Q r s - s * Q) := by ring
  have habs : |((s:ℤ) - s') * Q| < Q := by
    rw [key]
    calc |((r : ℤ) * goodOutcome Q r s - s' * Q) - ((r : ℤ) * goodOutcome Q r s - s * Q)|
        ≤ |(r : ℤ) * goodOutcome Q r s - s' * Q| + |(r : ℤ) * goodOutcome Q r s - s * Q| :=
          abs_sub _ _
      _ < Q := by linarith [abs_nonneg ((r : ℤ) * goodOutcome Q r s - s' * Q)]
  have hdvd : (Q:ℤ) ∣ ((s:ℤ) - s') * Q := ⟨(s:ℤ) - s', by ring⟩
  have hzero := Int.eq_zero_of_abs_lt_dvd hdvd habs
  have hQpos : (0:ℤ) < Q := by linarith [show (0:ℤ) < r by exact_mod_cast hr]
  have hss : (s:ℤ) = s' := by
    rcases mul_eq_zero.1 hzero with h1 | h1
    · linarith
    · linarith
  exact_mod_cast hss

theorem recovers_goodOutcome {Q r B s : ℕ} (hr : 0 < r) (hrB : r ≤ B) (hQ : 4 * B ^ 2 ≤ Q)
    (hs : Nat.Coprime r s) : Recovers B Q r (goodOutcome Q r s) := by
  have hB : 0 < B := lt_of_lt_of_le hr hrB
  have hQpos : 0 < Q := by nlinarith
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQpos
  have hBR : (0:ℝ) < B := by exact_mod_cast hB
  refine ⟨hr, hrB, s, hs, ?_⟩
  set y := goodOutcome Q r s with hy
  have hd := goodOutcome_spec (Q := Q) (r := r) (s := s) hr
  rw [← hy] at hd
  have key : (y:ℝ)/Q - (s:ℝ)/r = ((r:ℝ) * y - (s:ℝ) * Q) / ((r:ℝ) * Q) := by field_simp
  have habs : |(r:ℝ) * y - (s:ℝ) * Q| ≤ (r:ℝ)/2 := by
    have h2 : ((2 * |(r : ℤ) * (y:ℤ) - (s:ℤ) * Q| : ℤ) : ℝ) ≤ ((r:ℤ):ℝ) := by exact_mod_cast hd
    push_cast [Int.cast_abs] at h2
    linarith
  rw [key, abs_div, abs_of_pos (by positivity : (0:ℝ) < (r:ℝ) * Q)]
  have hQB : (4:ℝ) * (B:ℝ)^2 ≤ Q := by exact_mod_cast hQ
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [habs, sq_nonneg ((B:ℝ))]

/-! ## The distribution is a probability distribution -/

theorem prob_nonneg (Q r x0 y : ℕ) : 0 ≤ prob Q r x0 y := by
  unfold prob; positivity

/-- A nontrivial `Q`-th root of unity sums to zero over a full period. -/
theorem sum_exp_eq_zero (Q : ℕ) (c : ℤ) (hQ : 0 < Q) (hc : c ≠ 0) (hlt : |c| < Q) :
    ∑ y ∈ Finset.range Q, (Complex.exp (2 * (Real.pi:ℂ) * Complex.I * c / Q)) ^ y = 0 := by
  have hQC : (Q:ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hne : Complex.exp (2 * (Real.pi:ℂ) * Complex.I * c / Q) ≠ 1 := by
    intro hcon
    rw [Complex.exp_eq_one_iff] at hcon
    obtain ⟨n, hn⟩ := hcon
    have hpi : (Real.pi:ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact Real.pi_ne_zero
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    field_simp at hn
    have hz : c = Q * n := by exact_mod_cast hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp at hz; exact hc hz
    · have hge : (Q:ℤ) ≤ |c| := by
        rw [hz, abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ (Q:ℤ))]
        nlinarith [Int.one_le_abs hn0, (by positivity : (0:ℤ) ≤ (Q:ℤ))]
      omega
  rw [geom_sum_eq hne]
  have hpow : (Complex.exp (2 * (Real.pi:ℂ) * Complex.I * c / Q)) ^ Q = 1 := by
    rw [← Complex.exp_nat_mul]
    have hQr : (Q:ℂ) * (2 * (Real.pi:ℂ) * Complex.I * c / Q)
        = (c:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) := by field_simp
    rw [hQr, Complex.exp_int_mul_two_pi_mul_I]
  rw [hpow]
  simp

/-- Orthogonality computation: the squared moduli of the Fourier amplitudes over the
progression `{x₀ + j r : j < m}` sum to `m Q`, provided the progression does not wrap
around (`|(j - k) r| < Q` for `j ≠ k`). -/
theorem sum_norm_sq_geom (Q r x0 m : ℕ) (hQ : 0 < Q) (hr : 0 < r)
    (hspread : ∀ j k : ℕ, j < m → k < m → j ≠ k → |((j:ℤ) - k) * r| < Q) :
    ∑ y ∈ Finset.range Q, ‖∑ j ∈ Finset.range m,
      Complex.exp (2 * (Real.pi:ℂ) * Complex.I * (((x0:ℂ) + (j:ℂ) * (r:ℂ)) * (y:ℂ)) / (Q:ℂ))‖ ^ 2
      = (m:ℝ) * Q := by
  have hQC : (Q:ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hrZ : (r:ℤ) ≠ 0 := by positivity
  have hC : ((∑ y ∈ Finset.range Q, ‖∑ j ∈ Finset.range m,
      Complex.exp (2*(Real.pi:ℂ)*Complex.I*(((x0:ℂ) + (j:ℂ)*(r:ℂ))*(y:ℂ))/(Q:ℂ))‖^2 : ℝ) : ℂ)
      = ((m:ℝ) * Q : ℝ) := by
    push_cast
    have step1 : ∀ y : ℕ, ((‖∑ j ∈ Finset.range m,
        Complex.exp (2*(Real.pi:ℂ)*Complex.I*(((x0:ℂ) + (j:ℂ)*(r:ℂ))*(y:ℂ))/(Q:ℂ))‖ : ℝ) : ℂ)^2
        = ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m,
            (Complex.exp (2*(Real.pi:ℂ)*Complex.I*(((j:ℤ) - (k:ℤ))*(r:ℤ) : ℤ)/(Q:ℂ)))^y := by
      intro y
      rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum,
        Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_nat_mul]
      congr 1
      have hc : (starRingEnd ℂ) (2*(Real.pi:ℂ)*Complex.I*(((x0:ℂ) + (k:ℂ)*(r:ℂ))*(y:ℂ))/(Q:ℂ))
          = -(2*(Real.pi:ℂ)*Complex.I*(((x0:ℂ) + (k:ℂ)*(r:ℂ))*(y:ℂ))/(Q:ℂ)) := by
        simp [map_div₀, Complex.conj_I, map_ofNat]
        ring
      rw [hc]
      push_cast
      field_simp
      ring
    rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.range Q) => step1 y), Finset.sum_comm]
    have step2 : ∀ j ∈ Finset.range m, (∑ k ∈ Finset.range m, ∑ y ∈ Finset.range Q,
        (Complex.exp (2*(Real.pi:ℂ)*Complex.I*(((j:ℤ) - (k:ℤ))*(r:ℤ) : ℤ)/(Q:ℂ)))^y)
        = (Q:ℂ) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hinner : ∀ k ∈ Finset.range m, (∑ y ∈ Finset.range Q,
          (Complex.exp (2*(Real.pi:ℂ)*Complex.I*(((j:ℤ) - (k:ℤ))*(r:ℤ) : ℤ)/(Q:ℂ)))^y)
          = if j = k then (Q:ℂ) else 0 := by
        intro k hk
        rw [Finset.mem_range] at hk
        by_cases hjk : j = k
        · subst hjk; simp
        · rw [if_neg hjk]
          refine sum_exp_eq_zero Q (((j:ℤ) - k) * r) hQ ?_ (hspread j k hj hk hjk)
          exact mul_ne_zero (fun h0 => hjk (by omega)) hrZ
      rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq (Finset.range m) j (fun _ => (Q:ℂ))]
      simp [hj]
    have hfin : ∑ j ∈ Finset.range m, (∑ y ∈ Finset.range Q, ∑ k ∈ Finset.range m,
        (Complex.exp (2*(Real.pi:ℂ)*Complex.I*(((j:ℤ) - (k:ℤ))*(r:ℤ) : ℤ)/(Q:ℂ)))^y)
        = ∑ _j ∈ Finset.range m, (Q:ℂ) :=
      Finset.sum_congr rfl (fun j hj => by rw [Finset.sum_comm]; exact step2 j hj)
    rw [hfin]
    simp [mul_comm]
  exact_mod_cast hC

theorem prob_sum_eq_one {Q r x0 : ℕ} (hr : 0 < r) (hx0 : x0 < Q) :
    ∑ y ∈ Finset.range Q, prob Q r x0 y = 1 := by
  have hQpos : 0 < Q := by omega
  set m := numTerms Q r x0 with hmdef
  have hm : 0 < m := numTerms_pos hr hx0
  have hmr : (m:ℤ) * r ≤ (Q:ℤ) + r - 1 := by
    have hnat := numTerms_mul_le (Q := Q) (r := r) (x0 := x0) hr hx0
    have h1 : ((x0 + m * r : ℕ) : ℤ) ≤ ((Q + r - 1 : ℕ) : ℤ) := by exact_mod_cast hnat
    have h2 : ((Q + r - 1 : ℕ) : ℤ) = (Q:ℤ) + r - 1 := by
      have h3 : 1 ≤ Q + r := by omega
      push_cast [Nat.cast_sub h3]
      ring
    push_cast at h1
    rw [h2] at h1
    linarith [Int.natCast_nonneg x0]
  have hspread : ∀ j k : ℕ, j < m → k < m → j ≠ k → |((j:ℤ) - k) * (r:ℤ)| < Q := by
    intro j k hj hk hjk
    have hjk' : |((j:ℤ) - k)| ≤ (m:ℤ) - 1 := by rw [abs_le]; omega
    have hrZ : (0:ℤ) < r := by exact_mod_cast hr
    rw [abs_mul, abs_of_pos hrZ]
    nlinarith
  have hsum : ∑ y ∈ Finset.range Q, prob Q r x0 y =
      (∑ y ∈ Finset.range Q, ‖∑ j ∈ Finset.range m,
        Complex.exp (2*(Real.pi:ℂ)*Complex.I*(((x0:ℂ) + (j:ℂ)*(r:ℂ))*(y:ℂ))/(Q:ℂ))‖^2)
        / ((m:ℝ) * Q) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun y _ => prob_eq)
  rw [hsum, sum_norm_sq_geom Q r x0 m hQpos hr hspread, div_self]
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQpos
  positivity

/-! ## Main theorem -/

/-- **Shor's period finding.**  Let `r ≥ 1` be the period of the modular exponentiation
function `x ↦ a^x mod N`, let `B ≥ r` be a bound on the period known in advance and let the
quantum register size satisfy `Q ≥ 4B²`.  Whatever the outcome `x₀ < r` of the measurement of
the second register, the probability that the measured value `y` of the first register
determines the period (i.e. that the classical continued–fraction post-processing with
denominator bound `B` returns `r`) is at least `φ(r)/(6r)`. -/
theorem shor_period {Q r B x0 : ℕ} (hr : 0 < r) (hrB : r ≤ B) (hQ : 4 * B ^ 2 ≤ Q)
    (hx0 : x0 < r) :
    (r.totient : ℝ) / (6 * r) ≤
      ∑ y ∈ (Finset.range Q).filter (fun y => Recovers B Q r y), prob Q r x0 y := by
  have hrB2 : r ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hrB 2
  have hQr : 4 * r ^ 2 ≤ Q := le_trans (by omega) hQ
  have hr1 : 1 ≤ r := hr
  have hQlt : r < Q := by nlinarith
  set S : Finset ℕ := (Finset.range r).filter r.Coprime with hS
  set T : Finset ℕ := S.image (goodOutcome Q r) with hT
  have hsub : T ⊆ (Finset.range Q).filter (fun y => Recovers B Q r y) := by
    intro y hy
    rw [hT, Finset.mem_image] at hy
    obtain ⟨s, hsS, rfl⟩ := hy
    rw [hS, Finset.mem_filter, Finset.mem_range] at hsS
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨goodOutcome_lt hr hsS.1 (by omega), recovers_goodOutcome hr hrB hQ hsS.2⟩
  have hcard : S.card = r.totient := rfl
  have hsum : ∑ y ∈ T, prob Q r x0 y = ∑ s ∈ S, prob Q r x0 (goodOutcome Q r s) := by
    rw [hT]
    exact Finset.sum_image (fun a _ b _ hab => goodOutcome_injOn hr hQlt hab)
  have hterm : ∀ s ∈ S, 1 / (6 * (r:ℝ)) ≤ prob Q r x0 (goodOutcome Q r s) := by
    intro s _
    exact prob_lower_bound (s := s) (d := (r : ℤ) * goodOutcome Q r s - s * Q) hr hx0 hQr
      (goodOutcome_spec hr) (by ring)
  have hlow : (S.card : ℝ) * (1 / (6 * (r:ℝ))) ≤ ∑ s ∈ S, prob Q r x0 (goodOutcome Q r s) := by
    calc (S.card : ℝ) * (1 / (6 * (r:ℝ))) = ∑ _s ∈ S, 1 / (6 * (r:ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hterm
  have hfin : ∑ y ∈ T, prob Q r x0 y ≤
      ∑ y ∈ (Finset.range Q).filter (fun y => Recovers B Q r y), prob Q r x0 y :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => prob_nonneg _ _ _ _)
  have hrw : (r.totient : ℝ) / (6 * r) = (S.card : ℝ) * (1 / (6 * (r:ℝ))) := by
    rw [hcard]; ring
  rw [hrw]
  linarith [hsum ▸ hlow]

/-- **Shor's period finding for modular exponentiation.**  If `a` has finite order `r` (for
instance `a` a unit of `ZMod N`, so that `x ↦ a ^ x` is the modular exponentiation function
with period `r`), the second-register measurement returns `a ^ x₀` for some `x₀ < r` and
collapses the first register onto `{x < Q : a ^ x = a ^ x₀}` (`collapsed_register`).  The
subsequent Fourier measurement then yields, with probability at least `φ(r)/(6r)`, a value
`y` from which the classical post-processing returns the period `r`. -/
theorem shor_period_orderOf {G : Type*} [LeftCancelMonoid G] (a : G) {Q B x0 : ℕ}
    (h0 : 0 < orderOf a) (hrB : orderOf a ≤ B) (hQ : 4 * B ^ 2 ≤ Q) (hx0 : x0 < orderOf a) :
    ((orderOf a).totient : ℝ) / (6 * orderOf a) ≤
      ∑ y ∈ (Finset.range Q).filter (fun y => Recovers B Q (orderOf a) y),
        prob Q (orderOf a) x0 y :=
  shor_period h0 hrB hQ hx0

end QI

