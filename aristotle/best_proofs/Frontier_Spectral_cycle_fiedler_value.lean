/-
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the mandated
-- header above is written as a plain block comment; its text is verbatim.)

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

set_option grind.warning false

namespace Frontier.Spectral

open Finset Complex ZMod Matrix

/-! ## The Laplacian of the cycle graph -/

/-- The Laplacian matrix of the cycle graph `C n`, with vertex set `ZMod n`:
`2` on the diagonal, `-1` between neighbours `i` and `i ± 1`, `0` elsewhere. -/
noncomputable def cycleLaplacian (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℝ :=
  Matrix.of fun i j => if i = j then 2 else if i = j + 1 ∨ j = i + 1 then -1 else 0

/-- The set of Rayleigh quotients of the cycle Laplacian over nonzero vectors that are
orthogonal to the all-ones vector.  Its infimum is the algebraic connectivity (Fiedler value). -/
noncomputable def rayleighSet (n : ℕ) [NeZero n] : Set ℝ :=
  {r | ∃ x : ZMod n → ℝ, x ≠ 0 ∧ (∑ j, x j) = 0 ∧
      r = (x ⬝ᵥ (cycleLaplacian n *ᵥ x)) / (x ⬝ᵥ x)}

/-- The algebraic connectivity (Fiedler value) of the cycle graph `C n`: the second smallest
eigenvalue of its Laplacian, described variationally as the minimum of the Rayleigh quotient
over nonzero vectors orthogonal to the all-ones vector. -/
noncomputable def algebraicConnectivity (n : ℕ) [NeZero n] : ℝ := sInf (rayleighSet n)

/-! ## Basic facts about the standard additive character -/

section Char

variable {n : ℕ} [NeZero n]

lemma norm_stdAddChar (m : ZMod n) : ‖(stdAddChar m : ℂ)‖ = 1 := by
  rw [ZMod.stdAddChar_apply]; simp

lemma conj_stdAddChar (m : ZMod n) :
    (starRingEnd ℂ) (stdAddChar m) = stdAddChar (-m) := by
  rw [← Complex.inv_eq_conj (norm_stdAddChar m)]
  have h : (stdAddChar m : ℂ) * stdAddChar (-m) = 1 := by
    rw [← AddChar.map_add_eq_mul]; simp
  exact inv_eq_of_mul_eq_one_right h

lemma sum_stdAddChar (t : ZMod n) :
    ∑ i : ZMod n, (stdAddChar (t * i) : ℂ) = if t = 0 then (n : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n h)

lemma stdAddChar_re (m : ZMod n) :
    (stdAddChar m : ℂ).re = Real.cos (2 * Real.pi * m.val / n) := by
  have h : ((m.val : ℤ) : ZMod n) = m := by push_cast [ZMod.natCast_val]; simp
  have h2 : (stdAddChar m : ℂ) = Complex.exp (2 * Real.pi * I * ((m.val : ℤ) : ℂ) / n) := by
    rw [← ZMod.stdAddChar_coe, h]
  have h3 : (2 * (Real.pi : ℂ) * I * ((m.val : ℤ) : ℂ) / n)
      = ((2 * Real.pi * m.val / n : ℝ) : ℂ) * I := by push_cast; ring
  rw [h2, h3, Complex.exp_ofReal_mul_I_re]

end Char

/-! ## The Fourier (discrete) transform and Parseval -/

/-- Reindexing a sum over `ZMod n` by the shift `j ↦ j + 1`. -/
lemma sum_shift {n : ℕ} [NeZero n] {M : Type*} [AddCommMonoid M] (f : ZMod n → M) :
    ∑ j : ZMod n, f (j + 1) = ∑ j : ZMod n, f j :=
  Fintype.sum_equiv (Equiv.addRight (1 : ZMod n)) _ _ (fun _ => rfl)

/-- Unnormalised discrete Fourier transform on `ZMod n`. -/
noncomputable def dftAux (n : ℕ) [NeZero n] (x : ZMod n → ℂ) (k : ZMod n) : ℂ :=
  ∑ j : ZMod n, (stdAddChar (j * k) : ℂ) * x j

section Fourier

variable {n : ℕ} [NeZero n]

lemma dftAux_zero (x : ZMod n → ℂ) : dftAux n x 0 = ∑ j, x j := by
  simp [dftAux]

lemma dftAux_parseval (x : ZMod n → ℂ) :
    ∑ k : ZMod n, ‖dftAux n x k‖ ^ 2 = n * ∑ j : ZMod n, ‖x j‖ ^ 2 := by
  have expand : ∀ k : ZMod n, dftAux n x k * (starRingEnd ℂ) (dftAux n x k)
      = ∑ j : ZMod n, ∑ l : ZMod n,
          (stdAddChar ((j - l) * k) : ℂ) * (x j * (starRingEnd ℂ) (x l)) := by
    intro k
    rw [dftAux, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    have hconj : (starRingEnd ℂ) ((stdAddChar (l * k) : ℂ) * x l)
        = (stdAddChar (-(l * k)) : ℂ) * (starRingEnd ℂ) (x l) := by
      rw [RingHom.map_mul, conj_stdAddChar]
    have hc : (stdAddChar (j * k) : ℂ) * stdAddChar (-(l * k)) = stdAddChar ((j - l) * k) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [hconj, ← hc]; ring
  have swap : ∑ k : ZMod n, ∑ j : ZMod n, ∑ l : ZMod n,
        (stdAddChar ((j - l) * k) : ℂ) * (x j * (starRingEnd ℂ) (x l))
      = ∑ j : ZMod n, ∑ l : ZMod n, ∑ k : ZMod n,
        (stdAddChar ((j - l) * k) : ℂ) * (x j * (starRingEnd ℂ) (x l)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
  have main : ∑ k : ZMod n, dftAux n x k * (starRingEnd ℂ) (dftAux n x k)
      = (n : ℂ) * ∑ j : ZMod n, x j * (starRingEnd ℂ) (x j) := by
    rw [Finset.sum_congr rfl (fun k _ => expand k), swap, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have inner : ∀ l : ZMod n, ∑ k : ZMod n,
        (stdAddChar ((j - l) * k) : ℂ) * (x j * (starRingEnd ℂ) (x l))
        = (if l = j then (n : ℂ) else 0) * (x j * (starRingEnd ℂ) (x l)) := by
      intro l
      rw [← Finset.sum_mul, sum_stdAddChar]
      congr 1
      by_cases h : l = j
      · simp [h]
      · have hne : j - l ≠ 0 := fun hh => h (by linear_combination -hh)
        simp [h, hne]
    rw [Finset.sum_congr rfl (fun l _ => inner l)]
    simp
  have hL : ∑ k : ZMod n, dftAux n x k * (starRingEnd ℂ) (dftAux n x k)
      = ((∑ k : ZMod n, ‖dftAux n x k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [Complex.mul_conj, Complex.sq_norm])
  have hR : ∑ j : ZMod n, x j * (starRingEnd ℂ) (x j)
      = ((∑ j : ZMod n, ‖x j‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [Complex.mul_conj, Complex.sq_norm])
  rw [hL, hR] at main
  exact_mod_cast main

lemma dftAux_shift (x : ZMod n → ℂ) (k : ZMod n) :
    dftAux n (fun j => x j - x (j + 1)) k = (1 - (stdAddChar (-k) : ℂ)) * dftAux n x k := by
  have h1 : dftAux n (fun j => x j - x (j + 1)) k
      = dftAux n x k - ∑ j : ZMod n, (stdAddChar (j * k) : ℂ) * x (j + 1) := by
    rw [dftAux, dftAux, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have h2 : ∑ j : ZMod n, (stdAddChar (j * k) : ℂ) * x (j + 1)
      = (stdAddChar (-k) : ℂ) * dftAux n x k := by
    have hg := sum_shift (fun j : ZMod n => (stdAddChar ((j - 1) * k) : ℂ) * x j)
    simp only [add_sub_cancel_right] at hg
    rw [hg, dftAux, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hch : (stdAddChar ((j - 1) * k) : ℂ) = (stdAddChar (-k) : ℂ) * stdAddChar (j * k) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [hch]
    ring
  rw [h1, h2, dftAux]
  ring

end Fourier

/-! ## The spectral bound -/

lemma cos_le_cos_two_pi_div_aux (n v : ℕ) (h1 : 1 ≤ v) (h2 : 2 * v ≤ n) (hn : 3 ≤ n) :
    Real.cos (2 * Real.pi * v / n) ≤ Real.cos (2 * Real.pi / n) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hn
  have hv1 : (1:ℝ) ≤ v := by exact_mod_cast h1
  have hv2 : 2 * (v:ℝ) ≤ n := by exact_mod_cast h2
  apply Real.cos_le_cos_of_nonneg_of_le_pi
  · positivity
  · rw [div_le_iff₀ hn0]
    nlinarith [Real.pi_pos]
  · rw [div_le_div_iff_of_pos_right hn0]
    nlinarith [Real.pi_pos]

/-- For `1 ≤ v ≤ n - 1` the cosine `cos (2π v / n)` is at most `cos (2π / n)`. -/
lemma cos_le_cos_two_pi_div (n v : ℕ) (h1 : 1 ≤ v) (h2 : v ≤ n - 1) (hn : 3 ≤ n) :
    Real.cos (2 * Real.pi * v / n) ≤ Real.cos (2 * Real.pi / n) := by
  by_cases h : 2 * v ≤ n
  · exact cos_le_cos_two_pi_div_aux n v h1 h hn
  · have hvn : v ≤ n := by omega
    have hw : Real.cos (2 * Real.pi * v / n) = Real.cos (2 * Real.pi * (n - v : ℕ) / n) := by
      have hrw : (2 * Real.pi * ((n - v : ℕ) : ℝ) / n) = 2 * Real.pi - 2 * Real.pi * v / n := by
        have hcast : ((n - v : ℕ) : ℝ) = (n : ℝ) - v := by
          have := Nat.cast_sub hvn (R := ℝ); simpa using this
        rw [hcast]
        field_simp
      rw [hrw, Real.cos_two_pi_sub]
    rw [hw]
    exact cos_le_cos_two_pi_div_aux n (n - v) (by omega) (by omega) hn

lemma norm_one_sub_stdAddChar_sq {n : ℕ} [NeZero n] (m : ZMod n) :
    ‖1 - (stdAddChar m : ℂ)‖ ^ 2 = 2 - 2 * Real.cos (2 * Real.pi * m.val / n) := by
  have hz : Complex.normSq (stdAddChar m : ℂ) = 1 := by
    rw [← Complex.sq_norm, norm_stdAddChar]; norm_num
  rw [Complex.sq_norm, Complex.normSq_apply] at *
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, ← stdAddChar_re m]
  nlinarith [hz]

/-- The key spectral lower bound in complex form. -/
lemma cycle_energy_lower_bound {n : ℕ} [NeZero n] (hn : 3 ≤ n) (x : ZMod n → ℂ)
    (h0 : ∑ j, x j = 0) :
    (2 - 2 * Real.cos (2 * Real.pi / n)) * ∑ j, ‖x j‖ ^ 2 ≤ ∑ j, ‖x j - x (j + 1)‖ ^ 2 := by
  set mu := 2 - 2 * Real.cos (2 * Real.pi / n) with hmu
  have hpar1 := dftAux_parseval x
  have hpar2 := dftAux_parseval (fun j => x j - x (j + 1))
  have hterm : ∀ k : ZMod n,
      mu * ‖dftAux n x k‖ ^ 2 ≤ ‖dftAux n (fun j => x j - x (j + 1)) k‖ ^ 2 := by
    intro k
    rw [dftAux_shift, norm_mul, mul_pow, norm_one_sub_stdAddChar_sq]
    by_cases hk : k = 0
    · have hz : dftAux n x k = 0 := by rw [hk, dftAux_zero, h0]
      simp [hz]
    · have hnk : (-k) ≠ 0 := neg_ne_zero.mpr hk
      have hv1 : 1 ≤ (-k).val ∧ (-k).val ≤ n - 1 := by
        have h1 : (-k).val < n := ZMod.val_lt _
        have h2 : (-k).val ≠ 0 := fun hh => hnk ((ZMod.val_eq_zero _).mp hh)
        omega
      have hcos := cos_le_cos_two_pi_div n (-k).val hv1.1 hv1.2 hn
      have hnn : (0:ℝ) ≤ ‖dftAux n x k‖ ^ 2 := sq_nonneg _
      have hle : mu ≤ 2 - 2 * Real.cos (2 * Real.pi * (-k).val / n) := by
        simp only [hmu]; linarith
      exact mul_le_mul_of_nonneg_right hle hnn
  have hsum : mu * ∑ k : ZMod n, ‖dftAux n x k‖ ^ 2
      ≤ ∑ k : ZMod n, ‖dftAux n (fun j => x j - x (j + 1)) k‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hterm k)
  rw [hpar1, hpar2] at hsum
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hn
  nlinarith [hsum]

/-- Real form of the spectral lower bound. -/
lemma cycle_energy_lower_bound_real {n : ℕ} [NeZero n] (hn : 3 ≤ n) (x : ZMod n → ℝ)
    (h0 : ∑ j, x j = 0) :
    (2 - 2 * Real.cos (2 * Real.pi / n)) * ∑ j, (x j) ^ 2 ≤ ∑ j, (x j - x (j + 1)) ^ 2 := by
  have hc0 : ∑ j : ZMod n, ((x j : ℂ)) = 0 := by
    rw [← Complex.ofReal_sum, h0]; simp
  have h := cycle_energy_lower_bound hn (fun j => (x j : ℂ)) hc0
  have e1 : ∀ j : ZMod n, ‖((x j : ℂ))‖ ^ 2 = (x j) ^ 2 := by
    intro j; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have e2 : ∀ j : ZMod n, ‖((x j : ℂ)) - ((x (j + 1) : ℂ))‖ ^ 2 = (x j - x (j + 1)) ^ 2 := by
    intro j
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [e1, e2] at h
  exact h

/-! ## The quadratic form of the Laplacian -/

lemma one_ne_zero_zmod {n : ℕ} (hn : 3 ≤ n) : (1 : ZMod n) ≠ 0 := by
  have h : ((1 : ℕ) : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h; have := Nat.le_of_dvd one_pos h; omega
  simpa using h

lemma two_ne_zero_zmod {n : ℕ} (hn : 3 ≤ n) : (2 : ZMod n) ≠ 0 := by
  have h : ((2 : ℕ) : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  simpa using h

lemma cycleLaplacian_mulVec {n : ℕ} [NeZero n] (hn : 3 ≤ n) (x : ZMod n → ℝ) (i : ZMod n) :
    (cycleLaplacian n *ᵥ x) i = 2 * x i - x (i + 1) - x (i - 1) := by
  have h1 : (1 : ZMod n) ≠ 0 := one_ne_zero_zmod hn
  have h2 : (2 : ZMod n) ≠ 0 := two_ne_zero_zmod hn
  have hne1 : i + 1 ≠ i := by intro h; apply h1; linear_combination h
  have hne2 : i - 1 ≠ i := by intro h; apply h1; linear_combination -h
  have hne3 : i + 1 ≠ i - 1 := by intro h; apply h2; linear_combination h
  have key : ∀ j : ZMod n, cycleLaplacian n i j * x j =
      (if j = i then 2 * x j else 0) + (if j = i + 1 then -x j else 0)
        + (if j = i - 1 then -x j else 0) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp [cycleLaplacian, Ne.symm hne1, Ne.symm hne2]
    · by_cases hj2 : j = i + 1
      · subst hj2
        simp [cycleLaplacian, hji, hne3, h1]
      · by_cases hj3 : j = i - 1
        · subst hj3
          have e1 : i = i - 1 + 1 := by ring
          simp [cycleLaplacian, hji, hj2, ← e1, Ne.symm hne2]
        · have c1 : i ≠ j := fun h => hji h.symm
          have c2 : ¬ (i = j + 1) := by
            intro h; exact hj3 (by rw [h]; ring)
          simp [cycleLaplacian, c1, c2, hji, hj2, hj3]
  rw [Matrix.mulVec]
  simp only [dotProduct, key, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ]
  simp
  ring

lemma cycle_quadratic_form {n : ℕ} [NeZero n] (hn : 3 ≤ n) (x : ZMod n → ℝ) :
    x ⬝ᵥ (cycleLaplacian n *ᵥ x) = ∑ j, (x j - x (j + 1)) ^ 2 := by
  have hstep : x ⬝ᵥ (cycleLaplacian n *ᵥ x)
      = ∑ i : ZMod n, x i * (2 * x i - x (i + 1) - x (i - 1)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [cycleLaplacian_mulVec hn x i]
  rw [hstep]
  have e1 : ∑ i : ZMod n, x (i + 1) ^ 2 = ∑ i : ZMod n, x i ^ 2 := sum_shift (fun j => x j ^ 2)
  have e2 : ∑ i : ZMod n, x i * x (i - 1) = ∑ i : ZMod n, x i * x (i + 1) := by
    have h := sum_shift (fun j => x j * x (j - 1))
    simp only [add_sub_cancel_right] at h
    rw [← h]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have L : ∑ i : ZMod n, x i * (2 * x i - x (i + 1) - x (i - 1))
      = 2 * (∑ i : ZMod n, x i ^ 2) - (∑ i : ZMod n, x i * x (i + 1))
        - ∑ i : ZMod n, x i * x (i - 1) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have R : ∑ j : ZMod n, (x j - x (j + 1)) ^ 2
      = (∑ i : ZMod n, x i ^ 2) - 2 * (∑ i : ZMod n, x i * x (i + 1))
        + ∑ i : ZMod n, x (i + 1) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [L, R, e1, e2]
  ring

/-! ## The Fiedler eigenvector -/

/-- The candidate Fiedler eigenvector `j ↦ cos (2π j / n)`. -/
noncomputable def fiedlerVec (n : ℕ) [NeZero n] : ZMod n → ℝ := fun j => (stdAddChar j : ℂ).re

lemma fiedlerVec_sum {n : ℕ} [NeZero n] (hn : 3 ≤ n) : ∑ j, fiedlerVec n j = 0 := by
  have h : ∑ j : ZMod n, (stdAddChar ((1 : ZMod n) * j) : ℂ) = 0 := by
    rw [sum_stdAddChar]; simp [one_ne_zero_zmod hn]
  simp only [one_mul] at h
  have hre := congrArg Complex.re h
  rw [Complex.re_sum] at hre
  simpa [fiedlerVec] using hre

lemma fiedlerVec_ne_zero {n : ℕ} [NeZero n] : fiedlerVec n ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [fiedlerVec] at h0

lemma fiedlerVec_eigen {n : ℕ} [NeZero n] (hn : 3 ≤ n) (i : ZMod n) :
    2 * fiedlerVec n i - fiedlerVec n (i + 1) - fiedlerVec n (i - 1)
      = (2 - 2 * Real.cos (2 * Real.pi / n)) * fiedlerVec n i := by
  have hval : (1 : ZMod n).val = 1 := by
    haveI : Fact (1 < n) := ⟨by omega⟩
    exact ZMod.val_one n
  have hc : (stdAddChar (1 : ZMod n) : ℂ).re = Real.cos (2 * Real.pi / n) := by
    rw [stdAddChar_re, hval]; norm_num
  have hsum : (stdAddChar (i + 1) : ℂ) + stdAddChar (i - 1)
      = (stdAddChar i : ℂ) * (2 * (stdAddChar (1 : ZMod n) : ℂ).re) := by
    have e1 : (stdAddChar (i + 1) : ℂ) = stdAddChar i * stdAddChar (1 : ZMod n) := by
      rw [← AddChar.map_add_eq_mul]
    have e2 : (stdAddChar (i - 1) : ℂ) = stdAddChar i * stdAddChar (-(1 : ZMod n)) := by
      rw [← AddChar.map_add_eq_mul]; ring_nf
    rw [e1, e2, ← conj_stdAddChar, ← mul_add, Complex.add_conj]
    push_cast; ring
  have hre := congrArg Complex.re hsum
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat] at hre
  simp only [fiedlerVec, ← hc]
  linarith [hre]

lemma dotProduct_self_pos {n : ℕ} [NeZero n] {x : ZMod n → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
    ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

lemma fiedlerVec_mem_rayleighSet {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    (2 - 2 * Real.cos (2 * Real.pi / n)) ∈ rayleighSet n := by
  refine ⟨fiedlerVec n, fiedlerVec_ne_zero, fiedlerVec_sum hn, ?_⟩
  have hpos : 0 < fiedlerVec n ⬝ᵥ fiedlerVec n := dotProduct_self_pos fiedlerVec_ne_zero
  have hQ : fiedlerVec n ⬝ᵥ (cycleLaplacian n *ᵥ fiedlerVec n)
      = (2 - 2 * Real.cos (2 * Real.pi / n)) * (fiedlerVec n ⬝ᵥ fiedlerVec n) := by
    rw [dotProduct, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [cycleLaplacian_mulVec hn _ i, fiedlerVec_eigen hn i]
    ring
  rw [hQ]
  field_simp

/-- The all-ones vector spans the kernel direction: `0` is a Laplacian eigenvalue. -/
lemma cycleLaplacian_mulVec_const {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    cycleLaplacian n *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  funext i
  rw [cycleLaplacian_mulVec hn]
  norm_num

/-- `2 - 2 cos (2π/n)` really is an eigenvalue of the cycle Laplacian, with eigenvector
`fiedlerVec n`. -/
lemma cycleLaplacian_mulVec_fiedlerVec {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    cycleLaplacian n *ᵥ fiedlerVec n = (2 - 2 * Real.cos (2 * Real.pi / n)) • fiedlerVec n := by
  funext i
  rw [cycleLaplacian_mulVec hn, fiedlerVec_eigen hn i]
  simp

/-! ## Main theorem -/

/-- **Fiedler value of the cycle.**  For `n ≥ 3`, the algebraic connectivity (second smallest
Laplacian eigenvalue) of the cycle graph `C n` equals `2 - 2 cos (2π/n)`. -/
theorem cycle_fiedler_value (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    algebraicConnectivity n = 2 - 2 * Real.cos (2 * Real.pi / n) := by
  refine IsLeast.csInf_eq ⟨fiedlerVec_mem_rayleighSet hn, ?_⟩
  rintro r ⟨x, hx0, hxsum, rfl⟩
  have hpos : 0 < x ⬝ᵥ x := dotProduct_self_pos hx0
  rw [le_div_iff₀ hpos, cycle_quadratic_form hn x]
  have hb := cycle_energy_lower_bound_real hn x hxsum
  have hdp : x ⬝ᵥ x = ∑ j : ZMod n, (x j) ^ 2 :=
    Finset.sum_congr rfl (fun j _ => by rw [sq])
  rw [hdp]
  linarith [hb]

end Frontier.Spectral

-- Axiom audit: only the standard axioms of Lean/Mathlib are used.
#print axioms Frontier.Spectral.cycle_fiedler_value

