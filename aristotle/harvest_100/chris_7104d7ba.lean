/-
The quantum period-finding subroutine: the state produced by the algorithm,
the measurement distribution of the first register, and the lower bound on the
probability of a "good" measurement outcome.
-/
import Mathlib
import RequestProject.Analysis

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 2000000

namespace QI

/-- The primitive `Q`-th root of unity `e^{2πi/Q}` used by the quantum Fourier transform. -/
noncomputable def omega (Q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / Q)

theorem omega_eq (Q : ℕ) : omega Q = Complex.exp (((2 * Real.pi / Q : ℝ) : ℂ) * Complex.I) := by
  rw [omega]; congr 1; push_cast; ring

theorem norm_omega (Q : ℕ) : ‖omega Q‖ = 1 := by
  rw [omega_eq, Complex.norm_exp_ofReal_mul_I]

theorem omega_pow_eq (Q n : ℕ) :
    omega Q ^ n = Complex.exp (((2 * Real.pi * (n / Q : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rw [omega_eq, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- Only the residue of the exponent modulo `Q` matters: if `n = sQ + d` then
`ω^n = e^{2πi d/Q}`. -/
theorem omega_pow_int (Q n : ℕ) (s d : ℤ) (h : (n : ℤ) = s * Q + d) (hQ : 0 < Q) :
    omega Q ^ n = Complex.exp (((2 * Real.pi * (d / Q : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rw [omega_pow_eq]
  have hQc : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  have hn : (n : ℝ) = s * Q + d := by exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
  have key : ((2 * Real.pi * ((n : ℝ) / Q) : ℝ) : ℂ) * Complex.I
      = ((2 * Real.pi * ((d : ℝ) / Q) : ℝ) : ℂ) * Complex.I
        + (s : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hn]; push_cast; field_simp; ring
  rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

variable {β : Type*} [DecidableEq β]

/-- Amplitude of the computational basis state `|j⟩|y⟩` in the state
`Q^{-1/2} ∑_{j < Q} |j⟩|f j⟩` obtained by querying the oracle for `f`
(for Shor's algorithm `f j = a^j mod N`) on a uniform superposition. -/
noncomputable def oracleAmp (Q : ℕ) (f : ℕ → β) (j : ℕ) (y : β) : ℂ :=
  if j < Q ∧ f j = y then ((Real.sqrt Q : ℝ) : ℂ)⁻¹ else 0

/-- Amplitude of `|m⟩|y⟩` after applying the quantum Fourier transform modulo `Q`
to the first register. -/
noncomputable def qftAmp (Q : ℕ) (f : ℕ → β) (m : ℕ) (y : β) : ℂ :=
  ((Real.sqrt Q : ℝ) : ℂ)⁻¹ * ∑ j ∈ Finset.range Q, omega Q ^ (j * m) * oracleAmp Q f j y

/-- Probability of observing the value `m` when the first register is measured in
the computational basis. -/
noncomputable def measProb (Q : ℕ) (f : ℕ → β) (m : ℕ) : ℝ :=
  ∑ y ∈ (Finset.range Q).image f, ‖qftAmp Q f m y‖ ^ 2

theorem measProb_nonneg (Q : ℕ) (f : ℕ → β) (m : ℕ) : 0 ≤ measProb Q f m :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The number of `j < Q` in the residue class `k` modulo `r`. -/
def blockCount (Q r k : ℕ) : ℕ := (Q - k + r - 1) / r

theorem lt_blockCount_iff (Q r k l : ℕ) (hr : 0 < r) :
    l < blockCount Q r k ↔ k + l * r < Q := by
  rw [blockCount, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hr, add_mul, one_mul]
  generalize l * r = L
  omega

theorem inv_sqrt_sq (Q : ℕ) :
    ((Real.sqrt Q : ℝ) : ℂ)⁻¹ * ((Real.sqrt Q : ℝ) : ℂ)⁻¹ = (Q : ℂ)⁻¹ := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (Nat.cast_nonneg Q)]
  push_cast
  ring

theorem qftAmp_eq (Q : ℕ) (f : ℕ → β) (m : ℕ) (y : β) :
    qftAmp Q f m y =
      (Q : ℂ)⁻¹ * ∑ j ∈ (Finset.range Q).filter (fun j => f j = y), omega Q ^ (j * m) := by
  rw [qftAmp, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  have h : oracleAmp Q f j y = if f j = y then ((Real.sqrt Q : ℝ) : ℂ)⁻¹ else 0 := by
    rw [oracleAmp]; simp [hj]
  rw [h]
  by_cases hy : f j = y
  · simp only [hy, if_pos, ← inv_sqrt_sq Q]
    ring
  · simp [hy]

section Periodic

variable (f : ℕ → β) (Q r : ℕ)

/-- For a function with exact period `r`, the fibre of `f k` inside `[0, Q)` is an
arithmetic progression of step `r`. -/
theorem fiber_eq (k : ℕ) (hr : 0 < r) (hk : k < r)
    (hf : ∀ j k : ℕ, f j = f k ↔ j % r = k % r) :
    (Finset.range Q).filter (fun j => f j = f k) =
      (Finset.range (blockCount Q r k)).image (fun l => k + l * r) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hjQ, hfj⟩
    have hmod : j % r = k := by rw [hf] at hfj; rwa [Nat.mod_eq_of_lt hk] at hfj
    have hj : k + (j / r) * r = j := by
      conv_rhs => rw [← Nat.div_add_mod j r]
      rw [hmod]; ring
    exact ⟨j / r, by rw [lt_blockCount_iff Q r k _ hr, hj]; exact hjQ, hj⟩
  · rintro ⟨l, hl, rfl⟩
    rw [lt_blockCount_iff Q r k _ hr] at hl
    exact ⟨hl, by rw [hf, Nat.add_mul_mod_self_right]⟩

theorem image_range_eq (hr : 0 < r) (hrQ : r ≤ Q)
    (hf : ∀ j k : ℕ, f j = f k ↔ j % r = k % r) :
    (Finset.range Q).image f = (Finset.range r).image f := by
  apply Finset.Subset.antisymm
  · intro y hy
    simp only [Finset.mem_image, Finset.mem_range] at hy ⊢
    obtain ⟨j, hj, rfl⟩ := hy
    refine ⟨j % r, Nat.mod_lt _ hr, ?_⟩
    rw [hf, Nat.mod_mod_of_dvd _ dvd_rfl]
  · exact Finset.image_subset_image (by
      intro x hx; simp only [Finset.mem_range] at *; omega)

/-- The measurement distribution of the first register, expressed through the
`r` geometric sums coming from the residue classes modulo the period. -/
theorem measProb_eq (m : ℕ) (hr : 0 < r) (hrQ : r ≤ Q)
    (hf : ∀ j k : ℕ, f j = f k ↔ j % r = k % r) :
    measProb Q f m = ((Q : ℝ)⁻¹) ^ 2 *
      ∑ k ∈ Finset.range r,
        ‖∑ l ∈ Finset.range (blockCount Q r k), (omega Q ^ (r * m)) ^ l‖ ^ 2 := by
  have hinj : Set.InjOn f ↑(Finset.range r) := by
    intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    have := (hf x y).mp hxy
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  rw [measProb, image_range_eq f Q r hr hrQ hf, Finset.sum_image hinj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  have hinj2 : Set.InjOn (fun l => k + l * r) ↑(Finset.range (blockCount Q r k)) := by
    intro x _ y _ hxy
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_right hr (by omega)
  rw [qftAmp_eq, fiber_eq f Q r k hr hk hf, Finset.sum_image hinj2]
  have hterm : ∀ l : ℕ,
      omega Q ^ ((k + l * r) * m) = omega Q ^ (k * m) * (omega Q ^ (r * m)) ^ l := by
    intro l
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Finset.mul_sum, ← mul_assoc, norm_mul, norm_mul,
    mul_pow, mul_pow, norm_pow, norm_omega]
  simp

/-- **Key probability bound.**  If the measured value `m` is such that `r * m` is
within `r/2` of a multiple of `Q` (i.e. `m/Q` is within `1/(2Q)` of some `s/r`),
then `m` is observed with probability at least `1/(16 r)`. -/
theorem measProb_lower (m : ℕ) (hr : 0 < r) (h4 : 4 * r ≤ Q)
    (hf : ∀ j k : ℕ, f j = f k ↔ j % r = k % r)
    (s d : ℤ) (hd : ((r * m : ℕ) : ℤ) = s * Q + d) (hds : 2 * |d| ≤ r) :
    1 / (16 * (r : ℝ)) ≤ measProb Q f m := by
  have hpi := Real.pi_gt_three
  have hpi2 := Real.pi_lt_d2
  norm_num at hpi2
  have hQ0 : 0 < Q := by omega
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h5 : (4 : ℝ) * r ≤ Q := by exact_mod_cast h4
  set t : ℝ := (d : ℝ) / Q with ht
  have hzt : omega Q ^ (r * m) = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) :=
    omega_pow_int Q (r * m) s d hd hQ0
  have hdR : |(d : ℝ)| ≤ (r : ℝ) / 2 := by
    have : (2 : ℝ) * |(d : ℝ)| ≤ r := by exact_mod_cast hds
    linarith
  have htabs : |t| ≤ (r : ℝ) / (2 * Q) := by
    rw [ht, abs_div, abs_of_pos hQR, div_le_div_iff₀ hQR (by positivity)]
    nlinarith
  set A0 : ℕ := Q / r with hA0
  have hA0ge : (Q : ℝ) - r ≤ r * A0 := by
    have h3 : Q - r ≤ r * (Q / r) := by
      have h := Nat.div_add_mod Q r
      have h2 : Q % r < r := Nat.mod_lt _ hr
      omega
    have h3' : Q - r ≤ r * A0 := by rw [hA0]; exact h3
    have h4' := (Nat.cast_le (α := ℝ)).mpr h3'
    push_cast at h4'
    rw [Nat.cast_sub (by omega : r ≤ Q)] at h4'
    linarith
  have hkey : ∀ k ∈ Finset.range r, ((6 / (5 * Real.pi)) * A0) ^ 2 ≤
      ‖∑ l ∈ Finset.range (blockCount Q r k), (omega Q ^ (r * m)) ^ l‖ ^ 2 := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hA0le : A0 ≤ blockCount Q r k := by
      rw [blockCount, hA0]; exact Nat.div_le_div_right (by omega)
    have hblockle : (blockCount Q r k : ℝ) ≤ ((Q : ℝ) + r) / r := by
      rw [blockCount, le_div_iff₀ (by positivity)]
      have h1 : (Q - k + r - 1) / r * r ≤ Q - k + r - 1 := Nat.div_mul_le_self _ _
      have h2 : ((Q - k + r - 1) / r * r : ℕ) ≤ ((Q + r : ℕ) : ℝ) := by
        exact_mod_cast le_trans h1 (by omega)
      push_cast at h2 ⊢
      linarith
    have hbound : |(blockCount Q r k : ℝ) * t| ≤ 5 / 8 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (blockCount Q r k : ℝ))]
      have hmul : (blockCount Q r k : ℝ) * |t| ≤ (((Q : ℝ) + r) / r) * ((r : ℝ) / (2 * Q)) :=
        mul_le_mul hblockle htabs (abs_nonneg t) (by positivity)
      have heq : (((Q : ℝ) + r) / r) * ((r : ℝ) / (2 * Q)) = ((Q : ℝ) + r) / (2 * Q) := by
        field_simp
      rw [heq] at hmul
      have hlast : ((Q : ℝ) + r) / (2 * Q) ≤ 5 / 8 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 8)]
        linarith
      linarith
    rw [hzt]
    have hg := geom_norm_lower (blockCount Q r k) t hbound
    have hmono : (6 / (5 * Real.pi)) * A0 ≤ (6 / (5 * Real.pi)) * (blockCount Q r k) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast hA0le
    exact pow_le_pow_left₀ (by positivity) (le_trans hmono hg) 2
  rw [measProb_eq f Q r m hr (by omega) hf]
  have hsum : (r : ℝ) * ((6 / (5 * Real.pi)) * A0) ^ 2 ≤
      ∑ k ∈ Finset.range r, ‖∑ l ∈ Finset.range (blockCount Q r k), (omega Q ^ (r * m)) ^ l‖ ^ 2 := by
    calc (r : ℝ) * ((6 / (5 * Real.pi)) * A0) ^ 2
        = ∑ _k ∈ Finset.range r, ((6 / (5 * Real.pi)) * A0) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range]; simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hkey
  have hfinal : 1 / (16 * (r : ℝ)) ≤
      ((Q : ℝ)⁻¹) ^ 2 * ((r : ℝ) * ((6 / (5 * Real.pi)) * A0) ^ 2) := by
    have hA0pos : (0 : ℝ) ≤ A0 := by positivity
    have hkey2 : (3 : ℝ) / 4 * Q ≤ r * A0 := by linarith
    rw [div_le_iff₀ (by positivity)]
    have hexp : ((Q : ℝ)⁻¹) ^ 2 * ((r : ℝ) * ((6 / (5 * Real.pi)) * A0) ^ 2) * (16 * r)
        = (16 * 36 / (25 * Real.pi ^ 2)) * (((r : ℝ) * A0) ^ 2 / Q ^ 2) := by
      field_simp; ring
    rw [hexp]
    have h1 : (9 : ℝ) / 16 ≤ ((r : ℝ) * A0) ^ 2 / Q ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hp2 : Real.pi ^ 2 < 12.96 := by nlinarith
    have h2 : (1 : ℝ) ≤ (16 * 36 / (25 * Real.pi ^ 2)) * (9 / 16) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    have hc : (0 : ℝ) < 16 * 36 / (25 * Real.pi ^ 2) := by positivity
    calc (1 : ℝ) ≤ (16 * 36 / (25 * Real.pi ^ 2)) * (9 / 16) := h2
      _ ≤ (16 * 36 / (25 * Real.pi ^ 2)) * (((r : ℝ) * A0) ^ 2 / Q ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hc.le
  have hmul2 := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ ((Q : ℝ)⁻¹) ^ 2)
  linarith

end Periodic

end QI

/-
Analytic ingredients for the Shor period-finding proof:
norms of geometric sums of roots of unity and the Jordan-type sine bound.
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace QI

/-- `‖e^{ix} - 1‖ = 2|sin (x/2)|`. -/
theorem norm_exp_sub_one (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (x / 2)| := by
  have h1 : Complex.exp ((x : ℂ) * Complex.I) - 1 = ⟨Real.cos x - 1, Real.sin x⟩ := by
    rw [Complex.exp_mul_I]
    simp [Complex.ext_iff, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hx : Real.cos (2 * (x / 2)) = 2 * Real.cos (x / 2) ^ 2 - 1 := Real.cos_two_mul _
  rw [show 2 * (x / 2) = x by ring] at hx
  have h2 : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  rw [h1, Complex.norm_def, Complex.normSq_mk]
  have h3 : (Real.cos x - 1) * (Real.cos x - 1) + Real.sin x * Real.sin x
      = 4 * Real.sin (x / 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x, h2]
  rw [h3, show (4 : ℝ) * Real.sin (x / 2) ^ 2 = (2 * |Real.sin (x / 2)|) ^ 2 by
    rw [mul_pow, sq_abs]; ring]
  exact Real.sqrt_sq (by positivity)

theorem exp_eq_one_iff_sin_half (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) = 1 ↔ Real.sin (x / 2) = 0 := by
  constructor
  · intro h
    have h2 := norm_exp_sub_one x
    rw [h] at h2
    simpa using h2
  · intro h
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
    have hxk : x = 2 * k * Real.pi := by linarith
    rw [hxk, show ((2 * (k : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I
        = (k : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

/-- The Dirichlet-kernel identity, in a division-free form. -/
theorem norm_geom_sum_mul (A : ℕ) (x : ℝ) :
    ‖∑ l ∈ Finset.range A, Complex.exp ((x : ℂ) * Complex.I) ^ l‖ * |Real.sin (x / 2)| =
      |Real.sin (A * x / 2)| := by
  set z := Complex.exp ((x : ℂ) * Complex.I) with hz
  by_cases h : z = 1
  · have hs : Real.sin (x / 2) = 0 := (exp_eq_one_iff_sin_half x).mp h
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs
    have hxk : x = 2 * k * Real.pi := by linarith
    rw [hs, abs_zero, mul_zero, hxk,
      show (A : ℝ) * (2 * k * Real.pi) / 2 = ((A * k : ℤ) : ℝ) * Real.pi by push_cast; ring,
      Real.sin_int_mul_pi, abs_zero]
  · rw [geom_sum_eq h, norm_div]
    have hzA : z ^ A = Complex.exp ((((A : ℝ) * x : ℝ) : ℂ) * Complex.I) := by
      rw [hz, ← Complex.exp_nat_mul]; push_cast; ring_nf
    rw [hzA, norm_exp_sub_one, hz, norm_exp_sub_one]
    have hne : |Real.sin (x / 2)| ≠ 0 := by
      simp only [ne_eq, abs_eq_zero]
      exact fun h0 => h ((exp_eq_one_iff_sin_half x).mpr h0)
    field_simp

theorem sin_pi_lower_nonneg (u : ℝ) (hu : 0 ≤ u) (h : u ≤ 5 / 8) :
    (6 / 5) * u ≤ |Real.sin (Real.pi * u)| := by
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  rcases le_or_gt u (1 / 2) with h1 | h1
  · have h2 : Real.pi * u ≤ Real.pi / 2 := by nlinarith
    have h3 : 0 ≤ Real.pi * u := by positivity
    have hml := Real.mul_le_sin h3 h2
    have hs : 0 ≤ Real.sin (Real.pi * u) :=
      Real.sin_nonneg_of_nonneg_of_le_pi h3 (by nlinarith)
    rw [abs_of_nonneg hs]
    have he : 2 / Real.pi * (Real.pi * u) = 2 * u := by field_simp
    nlinarith
  · have key : Real.sin (Real.pi * u) = Real.sin (Real.pi * (1 - u)) := by
      rw [show Real.pi * (1 - u) = Real.pi - Real.pi * u by ring, Real.sin_pi_sub]
    have h3 : 0 ≤ Real.pi * (1 - u) := by nlinarith
    have h2 : Real.pi * (1 - u) ≤ Real.pi / 2 := by nlinarith
    have hb := Real.mul_le_sin h3 h2
    have he : 2 / Real.pi * (Real.pi * (1 - u)) = 2 * (1 - u) := by field_simp
    rw [key, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h3 (by nlinarith))]
    nlinarith

/-- A Jordan-type bound: `|sin (π u)| ≥ (6/5)|u|` for `|u| ≤ 5/8`. -/
theorem sin_pi_lower (u : ℝ) (h : |u| ≤ 5 / 8) : (6 / 5) * |u| ≤ |Real.sin (Real.pi * u)| := by
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu] at h ⊢
    exact sin_pi_lower_nonneg u hu h
  · rw [abs_of_nonpos hu] at h ⊢
    have := sin_pi_lower_nonneg (-u) (by linarith) h
    rwa [show Real.pi * -u = -(Real.pi * u) by ring, Real.sin_neg, abs_neg] at this

/-- Lower bound for the norm of a geometric sum of `A` powers of `e^{2πit}`,
valid as long as the total phase `A t` stays below `5/8`. -/
theorem geom_norm_lower (A : ℕ) (t : ℝ) (h : |(A : ℝ) * t| ≤ 5 / 8) :
    (6 / (5 * Real.pi)) * A ≤
      ‖∑ l ∈ Finset.range A, Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) ^ l‖ := by
  have hpi := Real.pi_gt_three
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_pow,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [Complex.norm_natCast]
    have : (6 : ℝ) / (5 * Real.pi) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) A]
  · have hid := norm_geom_sum_mul A (2 * Real.pi * t)
    rw [show (2 * Real.pi * t) / 2 = Real.pi * t by ring] at hid
    rw [show (A : ℝ) * (2 * Real.pi * t) / 2 = Real.pi * ((A : ℝ) * t) by ring] at hid
    have hlow := sin_pi_lower ((A : ℝ) * t) h
    have hup : |Real.sin (Real.pi * t)| ≤ Real.pi * |t| := by
      have := Real.abs_sin_le_abs (x := Real.pi * t)
      rwa [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.pi)] at this
    have hnn : 0 ≤ ‖∑ l ∈ Finset.range A,
        Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) ^ l‖ := norm_nonneg _
    set S := ‖∑ l ∈ Finset.range A,
      Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) ^ l‖
    have habs : |(A : ℝ) * t| = (A : ℝ) * |t| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg A)]
    have ht0 : 0 < |t| := abs_pos.mpr ht
    have h1 : (6 / 5) * ((A : ℝ) * |t|) ≤ S * (Real.pi * |t|) := by
      calc (6 / 5) * ((A : ℝ) * |t|) = (6 / 5) * |(A : ℝ) * t| := by rw [habs]
        _ ≤ |Real.sin (Real.pi * ((A : ℝ) * t))| := hlow
        _ = S * |Real.sin (Real.pi * t)| := hid.symm
        _ ≤ S * (Real.pi * |t|) := by nlinarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith

end QI

/-
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.Analysis
import RequestProject.Quantum

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

/-! ### Classical post-processing -/

/-- The classical post-processing of Shor's algorithm succeeds on the measurement
outcome `m`: some reduced fraction `p/q` with denominator `q ≤ N` lies within
`1/(2Q)` of `m/Q` (so the continued-fraction expansion of `m/Q` returns an answer),
and every such fraction has denominator exactly the period `r`. -/
def Recovers (N Q r m : ℕ) : Prop :=
  (∃ p q : ℕ, 0 < q ∧ q ≤ N ∧ Nat.Coprime p q ∧
      |(m : ℝ) / Q - (p : ℝ) / q| ≤ 1 / (2 * Q)) ∧
  (∀ p q : ℕ, 0 < q → q ≤ N → Nat.Coprime p q →
      |(m : ℝ) / Q - (p : ℝ) / q| ≤ 1 / (2 * Q) → q = r)

/-- The candidate measurement outcome nearest to `s·Q/r`, i.e. `round (s Q / r)`. -/
def bestM (Q r s : ℕ) : ℕ := (2 * s * Q + r) / (2 * r)

theorem bestM_close (Q r s : ℕ) (hr : 0 < r) :
    2 * |((r * bestM Q r s : ℕ) : ℤ) - (s : ℤ) * Q| ≤ (r : ℤ) := by
  have h2r : 0 < 2 * r := by omega
  have hdiv := Nat.div_add_mod (2 * s * Q + r) (2 * r)
  have hmod := Nat.mod_lt (2 * s * Q + r) h2r
  rw [bestM]
  set m := (2 * s * Q + r) / (2 * r) with hm
  set M := (2 * s * Q + r) % (2 * r) with hM
  have hz : (2 : ℤ) * r * m + M = 2 * s * Q + r := by exact_mod_cast hdiv
  have hMz : (M : ℤ) < 2 * r := by exact_mod_cast hmod
  have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
  push_cast
  have habs : (2 : ℤ) * |(r : ℤ) * m - s * Q| = |2 * ((r : ℤ) * m - s * Q)| := by
    rw [abs_mul]; norm_num
  rw [habs, abs_le]
  constructor <;> linarith

theorem bestM_lt (Q r s : ℕ) (hr : 0 < r) (hs : s < r) (hQ : 0 < Q) (hrQ : r ≤ Q) :
    bestM Q r s < Q := by
  have h2r : 0 < 2 * r := by omega
  have hdiv := Nat.div_add_mod (2 * s * Q + r) (2 * r)
  rw [bestM]
  set m := (2 * s * Q + r) / (2 * r) with hm
  have hle : (2 : ℤ) * r * m ≤ 2 * s * Q + r := by
    have : 2 * r * m ≤ 2 * s * Q + r := by omega
    exact_mod_cast this
  have hsz : (s : ℤ) + 1 ≤ r := by exact_mod_cast hs
  have hQz : (1 : ℤ) ≤ Q := by exact_mod_cast hQ
  have hrQz : (r : ℤ) ≤ Q := by exact_mod_cast hrQ
  have hrz : (1 : ℤ) ≤ r := by exact_mod_cast hr
  by_contra hcon
  push_neg at hcon
  have hmz : (Q : ℤ) ≤ m := by exact_mod_cast hcon
  nlinarith

/-- If `r m` is within `r/2` of `s Q`, then `m/Q` is within `1/(2Q)` of `s/r`. -/
theorem abs_div_sub_div_le (Q r s m : ℕ) (hr : 0 < r) (hQ : 0 < Q)
    (h : 2 * |((r * m : ℕ) : ℤ) - (s : ℤ) * Q| ≤ (r : ℤ)) :
    |(m : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * Q) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hR : 2 * |(r : ℝ) * m - (s : ℝ) * Q| ≤ (r : ℝ) := by
    have := (Int.cast_le (R := ℝ)).mpr h
    push_cast [Int.cast_abs] at this
    exact this
  have he : (m : ℝ) / Q - (s : ℝ) / r = ((r : ℝ) * m - (s : ℝ) * Q) / (r * Q) := by
    field_simp
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (r : ℝ) * Q),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [abs_nonneg ((r : ℝ) * m - (s : ℝ) * Q)]

/-- Two reduced fractions with denominators at most `N` that are both within
`1/(2Q)` of `m/Q` (with `Q ≥ 2N²`) must be equal. -/
theorem cross_mul_eq (N Q m r s p q : ℕ) (hQ : 2 * N ^ 2 ≤ Q) (hr : 0 < r) (hrN : r ≤ N)
    (hq : 0 < q) (hqN : q ≤ N)
    (h1 : |(m : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * Q))
    (h2 : |(m : ℝ) / Q - (p : ℝ) / q| ≤ 1 / (2 * Q)) :
    s * q = p * r := by
  have hN1 : 0 < N := lt_of_lt_of_le hr hrN
  have hQ0 : 0 < Q := by nlinarith
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdiff : |(s : ℝ) / r - (p : ℝ) / q| ≤ 1 / Q := by
    calc |(s : ℝ) / r - (p : ℝ) / q|
        = |((m : ℝ) / Q - (p : ℝ) / q) - ((m : ℝ) / Q - (s : ℝ) / r)| := by ring_nf
      _ ≤ |(m : ℝ) / Q - (p : ℝ) / q| + |(m : ℝ) / Q - (s : ℝ) / r| := abs_sub _ _
      _ ≤ 1 / (2 * Q) + 1 / (2 * Q) := by linarith
      _ = 1 / Q := by field_simp; norm_num
  have hprod : |(s : ℝ) * q - (p : ℝ) * r| ≤ (r * q) / Q := by
    have he : (s : ℝ) * q - (p : ℝ) * r = ((s : ℝ) / r - (p : ℝ) / q) * (r * q) := by field_simp
    rw [he, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (r : ℝ) * q)]
    calc |(s : ℝ) / r - (p : ℝ) / q| * (r * q) ≤ (1 / Q) * (r * q) :=
          mul_le_mul_of_nonneg_right hdiff (by positivity)
      _ = (r * q) / Q := by ring
  have hsmall : ((r : ℝ) * q) / Q ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hQR (by norm_num)]
    have hrn : (r : ℝ) ≤ N := by exact_mod_cast hrN
    have hqn : (q : ℝ) ≤ N := by exact_mod_cast hqN
    have hQn : 2 * (N : ℝ) ^ 2 ≤ Q := by exact_mod_cast hQ
    nlinarith [Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) q]
  have hlt : ((|(s * q : ℤ) - (p * r : ℤ)| : ℤ) : ℝ) < 1 := by
    rw [Int.cast_abs]
    push_cast
    linarith
  have hlt2 : |(s * q : ℤ) - (p * r : ℤ)| < 1 := by exact_mod_cast hlt
  rw [abs_lt] at hlt2
  have : (s * q : ℤ) = (p * r : ℤ) := by omega
  exact_mod_cast this

theorem den_eq_of_cross (s r p q : ℕ) (hs : Nat.Coprime s r) (hp : Nat.Coprime p q)
    (h : s * q = p * r) : q = r := by
  have h1 : r ∣ q := by
    have hd : r ∣ s * q := ⟨p, by rw [h]; ring⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hs) hd
  have h2 : q ∣ r := by
    have hd : q ∣ p * r := ⟨s, by rw [← h]; ring⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hp) hd
  exact Nat.dvd_antisymm h2 h1

/-- Two numerators giving the same nearest measurement outcome coincide. -/
theorem numerator_unique (Q r s s' m : ℕ) (hr : 0 < r) (hQ : 0 < Q) (hrQ : 2 * r ≤ Q)
    (h1 : |(m : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * Q))
    (h2 : |(m : ℝ) / Q - (s' : ℝ) / r| ≤ 1 / (2 * Q)) : s = s' := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrQR : 2 * (r : ℝ) ≤ Q := by exact_mod_cast hrQ
  have hdiff : |(s : ℝ) / r - (s' : ℝ) / r| ≤ 1 / Q := by
    calc |(s : ℝ) / r - (s' : ℝ) / r|
        = |((m : ℝ) / Q - (s' : ℝ) / r) - ((m : ℝ) / Q - (s : ℝ) / r)| := by ring_nf
      _ ≤ |(m : ℝ) / Q - (s' : ℝ) / r| + |(m : ℝ) / Q - (s : ℝ) / r| := abs_sub _ _
      _ ≤ 1 / (2 * Q) + 1 / (2 * Q) := by linarith
      _ = 1 / Q := by field_simp; norm_num
  have hprod : |(s : ℝ) - (s' : ℝ)| ≤ (r : ℝ) / Q := by
    have he : (s : ℝ) - (s' : ℝ) = ((s : ℝ) / r - (s' : ℝ) / r) * r := by field_simp
    rw [he, abs_mul, abs_of_pos hrR]
    calc |(s : ℝ) / r - (s' : ℝ) / r| * r ≤ (1 / Q) * r :=
          mul_le_mul_of_nonneg_right hdiff (by positivity)
      _ = (r : ℝ) / Q := by ring
  have hhalf : (r : ℝ) / Q ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hQR (by norm_num)]
    linarith
  have hlt : ((|(s : ℤ) - (s' : ℤ)| : ℤ) : ℝ) < 1 := by
    rw [Int.cast_abs]
    push_cast
    linarith
  have hlt2 : |(s : ℤ) - (s' : ℤ)| < 1 := by exact_mod_cast hlt
  rw [abs_lt] at hlt2
  omega

/-! ### The main theorem -/

/-- **Shor's period finding algorithm.**

Let `a` be invertible modulo `N > 1`, let `r` be the multiplicative order of `a`
modulo `N` (the period of `j ↦ a^j mod N`), and run the quantum period-finding
subroutine of Shor's algorithm with a first register of size `Q ≥ 2N²`: prepare
the uniform superposition over `j < Q`, query the oracle `j ↦ a^j mod N`, apply
the quantum Fourier transform modulo `Q` to the first register, and measure it.

Then with probability at least `φ(r)/(16 r)` the observed value `m` determines
the period: the classical continued-fraction post-processing of `m/Q` returns a
reduced fraction with denominator at most `N`, and every such fraction has
denominator exactly `r`. -/
theorem shor_period
    (N a Q : ℕ) (hN : 1 < N) (ha : Nat.Coprime a N) (hQ : 2 * N ^ 2 ≤ Q)
    (r : ℕ) (hr : r = orderOf (ZMod.unitOfCoprime a ha)) :
    (Nat.totient r : ℝ) / (16 * r) ≤
      ∑ m ∈ (Finset.range Q).filter (fun m => Recovers N Q r m),
        measProb Q (fun j => (a : ZMod N) ^ j) m := by
  haveI : NeZero N := ⟨by omega⟩
  set f : ℕ → ZMod N := fun j => (a : ZMod N) ^ j with hfdef
  -- basic facts about the period
  have hr0 : 0 < r := by rw [hr]; exact orderOf_pos _
  have hrN : r < N := by
    rw [hr]
    calc orderOf (ZMod.unitOfCoprime a ha) ≤ Nat.card (ZMod N)ˣ := orderOf_le_card
      _ = Nat.totient N := by simp [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
      _ < N := Nat.totient_lt N hN
  have hN2 : 2 ≤ N := hN
  have hQ0 : 0 < Q := by nlinarith
  have hrQ : 4 * r ≤ Q := by nlinarith
  have hf : ∀ j k : ℕ, f j = f k ↔ j % r = k % r := by
    intro j k
    have hcoe : ((ZMod.unitOfCoprime a ha : (ZMod N)ˣ) : ZMod N) = (a : ZMod N) :=
      ZMod.coe_unitOfCoprime a ha
    rw [hfdef]
    constructor
    · intro h
      have hu : (ZMod.unitOfCoprime a ha) ^ j = (ZMod.unitOfCoprime a ha) ^ k := by
        apply Units.ext
        push_cast
        rw [hcoe]
        exact h
      rw [hr]
      exact pow_eq_pow_iff_modEq.mp hu
    · intro h
      rw [hr] at h
      have hu : (ZMod.unitOfCoprime a ha) ^ j = (ZMod.unitOfCoprime a ha) ^ k :=
        pow_eq_pow_iff_modEq.mpr h
      have := congrArg (fun u : (ZMod N)ˣ => (u : ZMod N)) hu
      simpa [hcoe] using this
  -- the set of numerators s coprime to r
  set S : Finset ℕ := (Finset.range r).filter (fun s => Nat.Coprime r s) with hS
  have hScard : S.card = Nat.totient r := by rw [hS, Nat.totient]
  -- each such s gives a good measurement outcome
  have hclose : ∀ s : ℕ, |((bestM Q r s : ℕ) : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * Q) :=
    fun s => abs_div_sub_div_le Q r s (bestM Q r s) hr0 hQ0 (bestM_close Q r s hr0)
  have hrec : ∀ s ∈ S, Recovers N Q r (bestM Q r s) := by
    intro s hs
    rw [hS, Finset.mem_filter, Finset.mem_range] at hs
    obtain ⟨hslt, hscop⟩ := hs
    refine ⟨⟨s, r, hr0, hrN.le, Nat.Coprime.symm hscop, hclose s⟩, ?_⟩
    intro p q hq hqN hcop happ
    exact den_eq_of_cross s r p q (Nat.Coprime.symm hscop) hcop
      (cross_mul_eq N Q (bestM Q r s) r s p q hQ hr0 hrN.le hq hqN (hclose s) happ)
  -- the map s ↦ bestM Q r s is injective on S
  have hinj : Set.InjOn (bestM Q r) ↑S := by
    intro s hs s' hs' hEq
    rw [hS, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hs hs'
    refine numerator_unique Q r s s' (bestM Q r s) hr0 hQ0 (by omega) (hclose s) ?_
    rw [hEq]
    exact hclose s'
  -- the image lands in the set of successful outcomes
  have hsub : S.image (bestM Q r) ⊆ (Finset.range Q).filter (fun m => Recovers N Q r m) := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨s, hs, rfl⟩ := hm
    have hslt : s < r := by
      rw [hS, Finset.mem_filter, Finset.mem_range] at hs
      exact hs.1
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨bestM_lt Q r s hr0 hslt hQ0 (by omega), hrec s hs⟩
  -- lower bound for each good outcome
  have hlow : ∀ s ∈ S, 1 / (16 * (r : ℝ)) ≤ measProb Q f (bestM Q r s) := by
    intro s _
    refine measProb_lower f Q r (bestM Q r s) hr0 hrQ hf (s : ℤ)
      (((r * bestM Q r s : ℕ) : ℤ) - (s : ℤ) * Q) (by ring) ?_
    exact bestM_close Q r s hr0
  calc (Nat.totient r : ℝ) / (16 * r)
      = ∑ _s ∈ S, 1 / (16 * (r : ℝ)) := by
        rw [Finset.sum_const, hScard, nsmul_eq_mul]
        field_simp
    _ ≤ ∑ s ∈ S, measProb Q f (bestM Q r s) := Finset.sum_le_sum hlow
    _ = ∑ m ∈ S.image (bestM Q r), measProb Q f m := (Finset.sum_image hinj).symm
    _ ≤ ∑ m ∈ (Finset.range Q).filter (fun m => Recovers N Q r m), measProb Q f m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => measProb_nonneg Q f m)

end QI

