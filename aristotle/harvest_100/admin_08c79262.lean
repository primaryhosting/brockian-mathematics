/-
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a module doc-comment `/-! ... -/` before `import`,
-- so the required header appears above as an ordinary block comment.)

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## Elementary trigonometric estimates -/

/-- A crude but explicit linear lower bound for `sin` on `[0, 5π/8]`. -/
theorem sin_ge_two_fifths_mul (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 5 * Real.pi / 8) :
    (2 / 5) * x ≤ Real.sin x := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi' : Real.pi < 3.15 := Real.pi_lt_d2
  rcases le_or_gt x (Real.pi / 2) with h | h
  · have hs := Real.mul_le_sin h0 h
    have hle : (2 / 5 : ℝ) ≤ 2 / Real.pi := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
    nlinarith
  · have hx1 : 0 ≤ x - Real.pi / 2 := by linarith
    have hx2 : x - Real.pi / 2 ≤ Real.pi / 6 := by linarith
    have hcos : Real.cos (Real.pi / 6) ≤ Real.cos (x - Real.pi / 2) :=
      Real.cos_le_cos_of_nonneg_of_le_pi hx1 (by linarith) hx2
    have h6 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
    have h3 : (1.7 : ℝ) ≤ Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0), Real.sqrt_nonneg 3]
    have hsin : Real.sin x = Real.cos (x - Real.pi / 2) := by
      rw [Real.cos_sub_pi_div_two]
    rw [hsin]
    nlinarith

/-! ## The unit-modulus phase function -/

/-- `E t = e^{i t}`. -/
noncomputable def E (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

theorem E_add (s t : ℝ) : E (s + t) = E s * E t := by
  simp only [E, Complex.ofReal_add, add_mul, Complex.exp_add]

@[simp] theorem E_zero : E 0 = 1 := by simp [E]

@[simp] theorem norm_E (t : ℝ) : ‖E t‖ = 1 := by
  simp [E, Complex.norm_exp]

theorem E_int_two_pi (n : ℤ) : E (2 * Real.pi * n) = 1 := by
  have : ((2 * Real.pi * n : ℝ) : ℂ) * Complex.I = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [E, this, Complex.exp_int_mul_two_pi_mul_I]

theorem E_pow (t : ℝ) (n : ℕ) : E (t * n) = (E t) ^ n := by
  rw [E, E, ← Complex.exp_nat_mul]
  congr 1
  push_cast; ring

/-- `‖e^{ix} - 1‖ = 2 |sin (x/2)|`. -/
theorem norm_E_sub_one (x : ℝ) : ‖E x - 1‖ = 2 * |Real.sin (x / 2)| := by
  have h1 : E x - 1 = ⟨Real.cos x - 1, Real.sin x⟩ := by
    rw [E, Complex.exp_mul_I]
    apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have hc : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    have h2 : Real.cos (2 * (x / 2)) = Real.cos (x / 2) ^ 2 - Real.sin (x / 2) ^ 2 :=
      Real.cos_two_mul' _
    rw [show 2 * (x / 2) = x by ring] at h2
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  have hs : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  rw [h1, Complex.norm_def, Complex.normSq_mk]
  have key : (Real.cos x - 1) * (Real.cos x - 1) + Real.sin x * Real.sin x
      = (2 * |Real.sin (x / 2)|) ^ 2 := by
    rw [hc, hs, mul_pow, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  rw [key]
  exact Real.sqrt_sq (by positivity)

theorem norm_E_sub_one_le (x : ℝ) : ‖E x - 1‖ ≤ |x| := by
  rw [norm_E_sub_one]
  have := Real.abs_sin_le_abs (x := x / 2)
  rw [abs_div] at this
  simp only [Nat.abs_ofNat] at this
  linarith [this]

theorem norm_E_sub_one_ge (x : ℝ) (hx : |x| ≤ 5 * Real.pi / 4) :
    (2 / 5) * |x| ≤ ‖E x - 1‖ := by
  rw [norm_E_sub_one]
  have hpi := Real.pi_pos
  have hy : |x| / 2 ≤ Real.pi := by linarith
  have hs0 : 0 ≤ Real.sin (|x| / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hy
  have habs : |Real.sin (x / 2)| = Real.sin (|x| / 2) := by
    rcases le_or_gt 0 x with h | h
    · have hx' : |x| = x := abs_of_nonneg h
      rw [hx'] at hs0 ⊢
      exact abs_of_nonneg hs0
    · have hx' : |x| = -x := abs_of_neg h
      rw [hx'] at hs0 ⊢
      rw [show -x / 2 = -(x / 2) by ring, Real.sin_neg] at hs0 ⊢
      exact abs_of_nonpos (by linarith)
  rw [habs]
  have h1 : (2 / 5) * (|x| / 2) ≤ Real.sin (|x| / 2) := by
    refine sin_ge_two_fifths_mul _ (by positivity) ?_
    linarith
  linarith

/-! ## A lower bound for exponential sums -/

/-- If the total phase spread `A * |θ|` is at most `5π/4`, the geometric exponential sum
has norm at least `(2/5) A`. -/
theorem geom_E_lower (θ : ℝ) (A : ℕ) (h : |θ| * A ≤ 5 * Real.pi / 4) :
    (2 / 5) * (A : ℝ) ≤ ‖∑ j ∈ Finset.range A, E (θ * j)‖ := by
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · simp
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hθ : |θ| ≤ 5 * Real.pi / 4 := by
    nlinarith [abs_nonneg θ, Real.pi_pos]
  rcases eq_or_ne θ 0 with rfl | hθ0
  · simp only [zero_mul, E_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [Complex.norm_natCast]
    linarith
  · have hne : E θ ≠ 1 := by
      intro hEq
      have : ‖E θ - 1‖ = 0 := by rw [hEq]; simp
      have hlow := norm_E_sub_one_ge θ hθ
      rw [this] at hlow
      have : |θ| ≤ 0 := by linarith
      exact hθ0 (abs_eq_zero.mp (le_antisymm this (abs_nonneg θ)))
    have hsum : ∑ j ∈ Finset.range A, E (θ * j) = (E (θ * A) - 1) / (E θ - 1) := by
      have : ∀ j ∈ Finset.range A, E (θ * j) = (E θ) ^ j := fun j _ => E_pow θ j
      rw [Finset.sum_congr rfl this, geom_sum_eq hne, ← E_pow]
    rw [hsum, norm_div]
    have hden : ‖E θ - 1‖ ≤ |θ| := norm_E_sub_one_le θ
    have hnum : (2 / 5) * |θ * A| ≤ ‖E (θ * A) - 1‖ := by
      refine norm_E_sub_one_ge _ ?_
      rw [abs_mul, Nat.abs_cast]
      exact h
    have hdenpos : 0 < ‖E θ - 1‖ := by
      rw [norm_pos_iff, sub_ne_zero]; exact hne
    rw [le_div_iff₀ hdenpos]
    have habs : |θ * (A : ℝ)| = |θ| * A := by
      rw [abs_mul, Nat.abs_cast]
    rw [habs] at hnum
    calc (2 / 5) * (A : ℝ) * ‖E θ - 1‖ ≤ (2 / 5) * (A : ℝ) * |θ| := by
          apply mul_le_mul_of_nonneg_left hden (by positivity)
      _ = (2 / 5) * (|θ| * A) := by ring
      _ ≤ ‖E (θ * A) - 1‖ := hnum

theorem E_shift (t : ℝ) (n : ℤ) : E (t + 2 * Real.pi * n) = E t := by
  rw [E_add, E_int_two_pi, mul_one]

/-! ## The Shor measurement distribution

The first register is prepared in the uniform superposition over `x < Q`, the oracle writes
`f x` in the second register, and the quantum Fourier transform of order `Q` is applied to the
first register.  `amp Q f c y` is the resulting amplitude of the basis state `|c⟩|y⟩` and
`prob Q f c` is the probability that measuring the first register yields `c`. -/

/-- Amplitude of `|c⟩ ⊗ |y⟩` after the quantum Fourier transform in Shor's algorithm. -/
noncomputable def amp (Q : ℕ) (f : ℕ → ℕ) (c y : ℕ) : ℂ :=
  (Q : ℂ)⁻¹ * ∑ x ∈ (Finset.range Q).filter (fun x => f x = y), E (2 * Real.pi * c * x / Q)

/-- Probability that measuring the first register in Shor's algorithm returns `c`. -/
noncomputable def prob (Q : ℕ) (f : ℕ → ℕ) (c : ℕ) : ℝ :=
  ∑ y ∈ (Finset.range Q).image f, ‖amp Q f c y‖ ^ 2

theorem prob_nonneg (Q : ℕ) (f : ℕ → ℕ) (c : ℕ) : 0 ≤ prob Q f c :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ## Structure of the fibres of a periodic function -/

/-- The number of elements of `{x < Q | x ≡ x₀ [MOD r]}`, for `x₀ < r`. -/
def Acnt (Q r x0 : ℕ) : ℕ := (Q - x0 + (r - 1)) / r

theorem f_add_mul {f : ℕ → ℕ} {r : ℕ} (hper : ∀ x, f (x + r) = f x) (x k : ℕ) :
    f (x + k * r) = f x := by
  induction k with
  | zero => simp
  | succ n ih =>
    have : x + (n + 1) * r = (x + n * r) + r := by ring
    rw [this, hper, ih]

theorem f_mod {f : ℕ → ℕ} {r : ℕ} (hper : ∀ x, f (x + r) = f x) (x : ℕ) :
    f (x % r) = f x := by
  conv_rhs => rw [show x = x % r + (x / r) * r by rw [Nat.mod_add_div']]
  rw [f_add_mul hper]

theorem lt_Acnt_iff {Q r x0 : ℕ} (hr : 0 < r) (j : ℕ) :
    j < Acnt Q r x0 ↔ x0 + j * r < Q := by
  unfold Acnt
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hr, add_mul, one_mul]
  omega

theorem fiber_eq {f : ℕ → ℕ} {r Q : ℕ} (hr : 0 < r) (hrQ : r ≤ Q)
    (hper : ∀ x, f (x + r) = f x)
    (hinj : ∀ x y, x < r → y < r → f x = f y → x = y)
    {x0 : ℕ} (hx0 : x0 < r) :
    (Finset.range Q).filter (fun x => f x = f x0)
      = (Finset.range (Acnt Q r x0)).image (fun j => x0 + j * r) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hxQ, hfx⟩
    have hmod : x % r = x0 := by
      apply hinj _ _ (Nat.mod_lt _ hr) hx0
      rw [f_mod hper, hfx]
    have hdm : x % r + (x / r) * r = x := Nat.mod_add_div' x r
    refine ⟨x / r, ?_, ?_⟩
    · rw [lt_Acnt_iff hr, ← hmod]
      omega
    · omega
  · rintro ⟨j, hj, rfl⟩
    rw [lt_Acnt_iff hr] at hj
    exact ⟨hj, by rw [add_comm x0 (j * r), ← f_add_mul hper x0 j, add_comm]⟩

end QI

