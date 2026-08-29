import Mathlib
/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

namespace Frontier.Spectral

open Finset ZMod

/-- The Laplacian matrix of the cycle graph `C n` on the vertex set `ZMod n`:
diagonal entries `2` (each vertex has degree `2`), and `-1` in position `(i, j)`
whenever `j = i + 1` or `j = i - 1`. -/
noncomputable def cycleLaplacian (n : ℕ) : Matrix (ZMod n) (ZMod n) ℝ :=
  fun i j => if i = j then 2 else if j = i + 1 ∨ j = i - 1 then -1 else 0

section Basic

variable {n : ℕ} [NeZero n]

/-- Action of the cycle Laplacian on a vector. -/
lemma cycleLaplacian_mulVec (h3 : 3 ≤ n) (v : ZMod n → ℝ) (i : ZMod n) :
    (cycleLaplacian n).mulVec v i = 2 * v i - v (i + 1) - v (i - 1) := by
  have h1 : (1 : ZMod n) ≠ 0 := by
    have : ((1 : ℕ) : ZMod n) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h; have := Nat.le_of_dvd one_pos h; omega
    simpa using this
  have h2 : (2 : ZMod n) ≠ 0 := by
    have : ((2 : ℕ) : ZMod n) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h; have := Nat.le_of_dvd two_pos h; omega
    simpa using this
  have key : ∀ j : ZMod n, cycleLaplacian n i j * v j =
      (if j = i then 2 * v j else 0) + (if j = i + 1 then -v j else 0) +
        (if j = i - 1 then -v j else 0) := by
    intro j
    unfold cycleLaplacian
    by_cases hji : j = i
    · subst hji
      have e1 : j ≠ j + 1 := by intro h; exact h1 (by linear_combination -h)
      have e2 : j ≠ j - 1 := by intro h; exact h1 (by linear_combination h)
      simp [e1, e2]
    · have hij : i ≠ j := Ne.symm hji
      by_cases hj1 : j = i + 1
      · subst hj1
        have e2 : i + 1 ≠ i - 1 := by intro h; exact h2 (by linear_combination h)
        simp [hji, e2, hij]
      · by_cases hj2 : j = i - 1
        · subst hj2; simp [hji, hj1, hij]
        · simp [hji, hj1, hj2, hij]
  rw [Matrix.mulVec, dotProduct]
  simp only [key]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp
  ring

omit [NeZero n] in
/-- The cycle Laplacian is a symmetric matrix. -/
lemma cycleLaplacian_symm (i j : ZMod n) : cycleLaplacian n i j = cycleLaplacian n j i := by
  unfold cycleLaplacian
  have hiff : (j = i + 1 ∨ j = i - 1) ↔ (i = j + 1 ∨ i = j - 1) := by
    constructor
    · rintro (h | h)
      · exact Or.inr (by rw [h]; ring)
      · exact Or.inl (by rw [h]; ring)
    · rintro (h | h)
      · exact Or.inr (by rw [h]; ring)
      · exact Or.inl (by rw [h]; ring)
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h, hiff]

/-- The all-ones vector lies in the kernel of the cycle Laplacian: the row sums vanish. -/
lemma cycleLaplacian_mulVec_one (h3 : 3 ≤ n) :
    (cycleLaplacian n).mulVec (fun _ => (1 : ℝ)) = 0 := by
  funext i
  rw [cycleLaplacian_mulVec h3]
  norm_num

/-- Reindexing a sum over `ZMod n` by a shift. -/
lemma sum_shift {M : Type*} [AddCommMonoid M] (f : ZMod n → M) (a : ZMod n) :
    ∑ i : ZMod n, f (i + a) = ∑ i : ZMod n, f i :=
  Equiv.sum_comp (Equiv.addRight a) f

/-- The Laplacian quadratic form of the cycle is the sum of squared edge differences. -/
lemma cycleLaplacian_quadratic_form (h3 : 3 ≤ n) (v : ZMod n → ℝ) :
    ∑ i : ZMod n, v i * (cycleLaplacian n).mulVec v i
      = ∑ i : ZMod n, (v i - v (i + 1)) ^ 2 := by
  have hshift1 : ∑ i : ZMod n, v (i + 1) ^ 2 = ∑ i : ZMod n, v i ^ 2 :=
    sum_shift (fun i => v i ^ 2) 1
  have hshift2 : ∑ i : ZMod n, v i * v (i - 1) = ∑ i : ZMod n, v i * v (i + 1) := by
    have := sum_shift (fun i => v i * v (i - 1)) 1
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  have hL : ∀ i : ZMod n, v i * (cycleLaplacian n).mulVec v i
      = 2 * v i ^ 2 - v i * v (i + 1) - v i * v (i - 1) := by
    intro i
    rw [cycleLaplacian_mulVec h3]
    ring
  have e1 : ∑ i : ZMod n, v i * (cycleLaplacian n).mulVec v i
      = 2 * (∑ i : ZMod n, v i ^ 2) - (∑ i : ZMod n, v i * v (i + 1))
        - ∑ i : ZMod n, v i * v (i + 1) := by
    simp only [hL]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hshift2, ← Finset.mul_sum]
  have e2 : ∑ i : ZMod n, (v i - v (i + 1)) ^ 2
      = (∑ i : ZMod n, v i ^ 2) - 2 * (∑ i : ZMod n, v i * v (i + 1))
        + ∑ i : ZMod n, v (i + 1) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, hshift1]
  ring

end Basic

section Character

variable {N : ℕ} [NeZero N]

/-- The standard additive character has modulus one, so complex conjugation inverts it. -/
lemma conj_stdAddChar (z : ZMod N) :
    (starRingEnd ℂ) (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
  rw [AddChar.map_neg_eq_inv, ← Complex.inv_eq_conj, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

lemma norm_stdAddChar (z : ZMod N) : ‖ZMod.stdAddChar z‖ = 1 := by
  rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

/-- Orthogonality relation for the standard additive character. -/
lemma sum_stdAddChar_mul (t : ZMod N) :
    ∑ k : ZMod N, ZMod.stdAddChar (t * k) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)

/-- Explicit real part of the standard additive character. -/
lemma stdAddChar_re (k : ZMod N) :
    (ZMod.stdAddChar k).re = Real.cos (2 * Real.pi * k.val / N) := by
  have hk : k = ((k.val : ℤ) : ZMod N) := by push_cast [ZMod.natCast_val]; simp
  have h1 : ZMod.stdAddChar k
      = Complex.exp (((2 * Real.pi * k.val / N : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [hk]
    rw [ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [h1, Complex.exp_ofReal_mul_I_re]

/-- For `z` of modulus one, `‖1 - z‖ ^ 2 = 2 - 2 * z.re`. -/
lemma norm_one_sub_sq {z : ℂ} (h : ‖z‖ = 1) : ‖1 - z‖ ^ 2 = 2 - 2 * z.re := by
  have h' : Complex.normSq z = 1 := by rw [← Complex.sq_norm, h]; norm_num
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply] at h' ⊢
  nlinarith [h']

end Character

section Fourier

open scoped ZMod

variable {N : ℕ} [NeZero N]

/-- Parseval's identity for the discrete Fourier transform on `ZMod N`. -/
lemma dft_parseval (u : ZMod N → ℂ) :
    ∑ k : ZMod N, ‖𝓕 u k‖ ^ 2 = (N : ℝ) * ∑ j : ZMod N, ‖u j‖ ^ 2 := by
  have main : ∑ k : ZMod N, (𝓕 u k) * (starRingEnd ℂ) (𝓕 u k)
      = (N : ℂ) * ∑ j : ZMod N, u j * (starRingEnd ℂ) (u j) := by
    calc ∑ k : ZMod N, (𝓕 u k) * (starRingEnd ℂ) (𝓕 u k)
        = ∑ k : ZMod N, ∑ j : ZMod N, ∑ l : ZMod N,
            (u j * (starRingEnd ℂ) (u l)) * ZMod.stdAddChar ((l - j) * k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ZMod.dft_apply]
          simp only [smul_eq_mul, map_sum, map_mul, conj_stdAddChar]
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
          rw [show ((l - j) * k) = (-(j * k)) + (-(-(l * k))) by ring, AddChar.map_add_eq_mul]
          ring
      _ = ∑ j : ZMod N, ∑ l : ZMod N, (u j * (starRingEnd ℂ) (u l)) *
            ∑ k : ZMod N, ZMod.stdAddChar ((l - j) * k) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => (Finset.mul_sum _ _ _).symm
      _ = (N : ℂ) * ∑ j : ZMod N, u j * (starRingEnd ℂ) (u j) := by
          simp only [sum_stdAddChar_mul, sub_eq_zero]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_eq_single j]
          · simp; ring
          · intro l _ hl; simp [hl]
          · simp
  have hcast : ((∑ k : ZMod N, ‖𝓕 u k‖ ^ 2 : ℝ) : ℂ)
      = (((N : ℝ) * ∑ j : ZMod N, ‖u j‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_natCast]
    simpa only [Complex.mul_conj, Complex.normSq_eq_norm_sq] using main
  exact_mod_cast hcast

/-- The discrete Fourier transform turns the cyclic difference into multiplication
by `1 - χ(k)`. -/
lemma dft_diff (u : ZMod N → ℂ) (k : ZMod N) :
    𝓕 (fun j => u j - u (j + 1)) k = (1 - ZMod.stdAddChar k) * 𝓕 u k := by
  simp only [ZMod.dft_apply, smul_eq_mul, mul_sub, sub_mul, one_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.subRight (1 : ZMod N))
    (fun j => ZMod.stdAddChar (-(j * k)) * u (j + 1))]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.subRight_apply, sub_add_cancel]
  rw [show (-((j - 1) * k)) = k + (-(j * k)) by ring, AddChar.map_add_eq_mul]
  ring

end Fourier

section Gap

/-- Monotonicity input: `cos (2πm/n) ≤ cos (2π/n)` for `1 ≤ m ≤ n - 1`. -/
lemma cos_le_cos_base {n m : ℕ} (hm : 1 ≤ m) (hmn : m + 1 ≤ n) :
    Real.cos (2 * Real.pi * m / n) ≤ Real.cos (2 * Real.pi / n) := by
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hpi := Real.pi_pos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
  set θ : ℝ := 2 * Real.pi * m / n with hθ
  have hbase : 0 ≤ 2 * Real.pi / n := by positivity
  rcases le_total θ Real.pi with h | h
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hbase h (by
      rw [hθ, div_le_div_iff_of_pos_right hn0]; nlinarith)
  · rw [show Real.cos θ = Real.cos (2 * Real.pi - θ) from (Real.cos_two_pi_sub θ).symm]
    refine Real.cos_le_cos_of_nonneg_of_le_pi hbase (by linarith) ?_
    have heq : 2 * Real.pi - θ = 2 * Real.pi * ((n : ℝ) - m) / n := by rw [hθ]; field_simp
    rw [heq, div_le_div_iff_of_pos_right hn0]
    nlinarith

variable {n : ℕ} [NeZero n]

/-- The nonzero Fourier modes all have `‖1 - χ(k)‖ ^ 2` at least the Fiedler value. -/
lemma fiedler_le_norm_one_sub_char {k : ZMod n} (hk : k ≠ 0) :
    2 - 2 * Real.cos (2 * Real.pi / n) ≤ ‖1 - ZMod.stdAddChar k‖ ^ 2 := by
  rw [norm_one_sub_sq (norm_stdAddChar k), stdAddChar_re]
  have hlt : k.val < n := ZMod.val_lt k
  have hpos : 1 ≤ k.val := by
    rcases Nat.eq_zero_or_pos k.val with h | h
    · exact absurd ((ZMod.val_eq_zero k).mp h) hk
    · exact h
  have := cos_le_cos_base (n := n) (m := k.val) hpos (by omega)
  linarith

end Gap

section LowerBound

open scoped ZMod

variable {n : ℕ} [NeZero n]

/-- Spectral gap inequality (complex form): for `u : ZMod n → ℂ` with vanishing mean,
the Dirichlet energy is at least the Fiedler value times the squared norm. -/
lemma energy_lower_bound_complex (h3 : 3 ≤ n) (u : ZMod n → ℂ) (hu : ∑ j : ZMod n, u j = 0) :
    (2 - 2 * Real.cos (2 * Real.pi / n)) * ∑ j : ZMod n, ‖u j‖ ^ 2
      ≤ ∑ j : ZMod n, ‖u j - u (j + 1)‖ ^ 2 := by
  set c : ℝ := 2 - 2 * Real.cos (2 * Real.pi / n) with hc
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hU0 : 𝓕 u 0 = 0 := by rw [ZMod.dft_apply_zero]; exact hu
  have hkey : ∀ k : ZMod n, c * ‖𝓕 u k‖ ^ 2 ≤ ‖𝓕 (fun j => u j - u (j + 1)) k‖ ^ 2 := by
    intro k
    rw [dft_diff, norm_mul, mul_pow]
    by_cases hk : k = 0
    · subst hk; simp [hU0]
    · exact mul_le_mul_of_nonneg_right (fiedler_le_norm_one_sub_char hk) (by positivity)
  have hsum : c * ∑ k : ZMod n, ‖𝓕 u k‖ ^ 2
      ≤ ∑ k : ZMod n, ‖𝓕 (fun j => u j - u (j + 1)) k‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hkey k
  rw [dft_parseval, dft_parseval] at hsum
  have := (mul_le_mul_iff_of_pos_left hn0).mp (by linarith : (n : ℝ) * (c * ∑ j : ZMod n, ‖u j‖ ^ 2)
    ≤ (n : ℝ) * ∑ j : ZMod n, ‖u j - u (j + 1)‖ ^ 2)
  exact this

/-- Spectral gap inequality (real form). -/
lemma energy_lower_bound_real (h3 : 3 ≤ n) (v : ZMod n → ℝ) (hv : ∑ j : ZMod n, v j = 0) :
    (2 - 2 * Real.cos (2 * Real.pi / n)) * ∑ j : ZMod n, (v j) ^ 2
      ≤ ∑ j : ZMod n, (v j - v (j + 1)) ^ 2 := by
  have hu : ∑ j : ZMod n, ((v j : ℂ)) = 0 := by
    rw [← Complex.ofReal_sum, hv, Complex.ofReal_zero]
  have := energy_lower_bound_complex h3 (fun j => (v j : ℂ)) hu
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs] using this

end LowerBound

section Eigenvector

variable {n : ℕ} [NeZero n]

/-- The Fiedler eigenvector of the cycle: the real part of the standard additive character. -/
noncomputable def fiedlerVector (n : ℕ) [NeZero n] : ZMod n → ℝ :=
  fun i => (ZMod.stdAddChar i).re

lemma fiedlerVector_ne_zero : fiedlerVector n ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [fiedlerVector] at h0

lemma sum_fiedlerVector (h3 : 3 ≤ n) : ∑ i : ZMod n, fiedlerVector n i = 0 := by
  have h : (1 : ZMod n) ≠ 0 := by
    rw [show (1 : ZMod n) = ((1 : ℕ) : ZMod n) by simp, Ne, ZMod.natCast_eq_zero_iff]
    intro hd; have := Nat.le_of_dvd one_pos hd; omega
  have h1 : ∑ i : ZMod n, ZMod.stdAddChar i
      = ∑ i : ZMod n, ZMod.stdAddChar ((1 : ZMod n) * i) := by simp
  have hzero : ∑ i : ZMod n, ZMod.stdAddChar i = 0 := by
    rw [h1, sum_stdAddChar_mul, if_neg h]
  unfold fiedlerVector
  rw [← Complex.re_sum, hzero, Complex.zero_re]

/-- The Fiedler vector is an eigenvector with eigenvalue `2 - 2 cos (2π/n)`. -/
lemma cycleLaplacian_mulVec_fiedlerVector (h3 : 3 ≤ n) :
    (cycleLaplacian n).mulVec (fiedlerVector n)
      = (2 - 2 * Real.cos (2 * Real.pi / n)) • fiedlerVector n := by
  have hn1 : 1 < n := by omega
  have hval : (1 : ZMod n).val = 1 := ZMod.val_one_eq_one_mod n ▸ Nat.mod_eq_of_lt hn1
  have hc : (ZMod.stdAddChar (1 : ZMod n)).re = Real.cos (2 * Real.pi / n) := by
    rw [stdAddChar_re, hval]
    norm_num
  funext i
  rw [cycleLaplacian_mulVec h3, Pi.smul_apply, smul_eq_mul]
  unfold fiedlerVector
  have e1 : ZMod.stdAddChar (i + 1) = ZMod.stdAddChar i * ZMod.stdAddChar (1 : ZMod n) :=
    AddChar.map_add_eq_mul (ZMod.stdAddChar) i 1
  have e2 : ZMod.stdAddChar (i - 1) = ZMod.stdAddChar i * ZMod.stdAddChar (-1 : ZMod n) := by
    rw [← AddChar.map_add_eq_mul (ZMod.stdAddChar) i (-1)]
    ring_nf
  have e3 : ZMod.stdAddChar (-(1 : ZMod n)) = (starRingEnd ℂ) (ZMod.stdAddChar 1) :=
    (conj_stdAddChar 1).symm
  rw [e1, e2, e3]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  rw [hc]
  ring

end Eigenvector

/-- A nonzero vector has positive squared norm. -/
lemma sum_sq_pos {n : ℕ} [NeZero n] {v : ZMod n → ℝ} (hv0 : v ≠ 0) :
    0 < ∑ i : ZMod n, (v i) ^ 2 := by
  rcases Function.ne_iff.mp hv0 with ⟨i, hi⟩
  refine Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  have hvi : v i ≠ 0 := by simpa using hi
  positivity

/-- **Fiedler value of the cycle graph.**
For `n ≥ 3`, the algebraic connectivity of the cycle `C n` — the least eigenvalue of the
Laplacian `cycleLaplacian n` among eigenvectors orthogonal to the all-ones vector — equals
`2 - 2 * cos (2π/n)`. -/
theorem cycle_fiedler_value (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    IsLeast {μ : ℝ | ∃ v : ZMod n → ℝ, v ≠ 0 ∧ (∑ i : ZMod n, v i = 0) ∧
        (cycleLaplacian n).mulVec v = μ • v}
      (2 - 2 * Real.cos (2 * Real.pi / n)) := by
  constructor
  · exact ⟨fiedlerVector n, fiedlerVector_ne_zero, sum_fiedlerVector hn,
      cycleLaplacian_mulVec_fiedlerVector hn⟩
  · rintro μ ⟨v, hv0, hvsum, hvL⟩
    have hpos : 0 < ∑ i : ZMod n, (v i) ^ 2 := sum_sq_pos hv0
    have hquad : ∑ i : ZMod n, v i * (cycleLaplacian n).mulVec v i = μ * ∑ i : ZMod n, (v i) ^ 2 := by
      rw [hvL]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply]; ring
    rw [cycleLaplacian_quadratic_form hn] at hquad
    have hlb := energy_lower_bound_real hn v hvsum
    rw [hquad] at hlb
    exact le_of_mul_le_mul_right (by linarith) hpos

/-- **Variational form of the Fiedler value of the cycle graph.**
For `n ≥ 3`, the minimum of the Rayleigh quotient of the cycle Laplacian over all nonzero
vectors orthogonal to the all-ones vector equals `2 - 2 * cos (2π/n)`. -/
theorem cycle_fiedler_value_rayleigh (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    IsLeast {r : ℝ | ∃ v : ZMod n → ℝ, v ≠ 0 ∧ (∑ i : ZMod n, v i = 0) ∧
        r = (∑ i : ZMod n, v i * (cycleLaplacian n).mulVec v i) / ∑ i : ZMod n, (v i) ^ 2}
      (2 - 2 * Real.cos (2 * Real.pi / n)) := by
  constructor
  · refine ⟨fiedlerVector n, fiedlerVector_ne_zero, sum_fiedlerVector hn, ?_⟩
    have hpos : 0 < ∑ i : ZMod n, (fiedlerVector n i) ^ 2 := sum_sq_pos fiedlerVector_ne_zero
    have hq : ∑ i : ZMod n, fiedlerVector n i * (cycleLaplacian n).mulVec (fiedlerVector n) i
        = (2 - 2 * Real.cos (2 * Real.pi / n)) * ∑ i : ZMod n, (fiedlerVector n i) ^ 2 := by
      rw [cycleLaplacian_mulVec_fiedlerVector hn, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply]; ring
    rw [hq]
    field_simp
  · rintro r ⟨v, hv0, hvsum, rfl⟩
    have hpos : 0 < ∑ i : ZMod n, (v i) ^ 2 := sum_sq_pos hv0
    rw [le_div_iff₀ hpos, cycleLaplacian_quadratic_form hn]
    exact energy_lower_bound_real hn v hvsum

end Frontier.Spectral

