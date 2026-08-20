import Mathlib

/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset Matrix

/-- The `n × n` quantum Fourier transform matrix, with entries
`exp (2 π i j k / n) / √n`. -/
noncomputable def qft (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k =>
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) * (k : ℕ)) / n) / (Real.sqrt n : ℝ)

lemma qft_apply (n : ℕ) (j k : Fin n) :
    qft n j k =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) * (k : ℕ)) / n) /
        (Real.sqrt n : ℝ) := rfl

lemma two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero

/-- Orthogonality of characters: the sum of `exp (2 π i k m / n)` over `k < n`
is `n` if `n ∣ m`, and `0` otherwise. -/
lemma sum_exp_eq (n : ℕ) (hn : 0 < n) (m : ℤ) :
    (∑ k : Fin n, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k : ℕ) * (m : ℂ)) / n))
      = if (n : ℤ) ∣ m then (n : ℂ) else 0 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  set x : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / n) with hx
  have hxk : ∀ k : ℕ,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k : ℕ) * (m : ℂ)) / n) = x ^ k := by
    intro k
    rw [hx, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  have hsum : (∑ k : Fin n, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k : ℕ) * (m : ℂ)) / n))
      = ∑ k ∈ Finset.range n, x ^ k := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => x ^ k) n]
    exact Finset.sum_congr rfl fun k _ => hxk k
  rw [hsum]
  by_cases hd : (n : ℤ) ∣ m
  · rw [if_pos hd]
    obtain ⟨t, ht⟩ := hd
    have hx1 : x = 1 := by
      have harg : 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / n
          = (t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        rw [ht]
        push_cast
        field_simp
      rw [hx, harg]
      exact Complex.exp_int_mul_two_pi_mul_I t
    simp [hx1]
  · rw [if_neg hd]
    have hxne : x ≠ 1 := by
      intro h
      rw [hx, Complex.exp_eq_one_iff] at h
      obtain ⟨t, ht⟩ := h
      rw [div_eq_iff hn0] at ht
      have h3 : (2 * (Real.pi : ℂ) * Complex.I) * (m : ℂ)
          = (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * (t : ℂ)) := by
        linear_combination ht
      have h4 : (m : ℂ) = ((n : ℂ) * (t : ℂ)) := mul_left_cancel₀ two_pi_I_ne_zero h3
      exact hd ⟨t, by exact_mod_cast h4⟩
    have hxn : x ^ n = 1 := by
      rw [hx, ← Complex.exp_nat_mul]
      have harg : (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / n)
          = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        field_simp
      rw [harg]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [geom_sum_eq hxne, hxn, sub_self, zero_div]

lemma qft_conjTranspose_mul (n : ℕ) (hn : 0 < n) : (qft n)ᴴ * (qft n) = 1 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsq : ((Real.sqrt n : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    norm_num
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ k : Fin n, (qft n)ᴴ j k * qft n k l
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((k : ℕ) * ((((l : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : ℂ)) / n) / n := by
    intro k
    rw [Matrix.conjTranspose_apply, qft_apply, qft_apply, Complex.star_def, map_div₀,
      ← Complex.exp_conj]
    simp only [Complex.conj_ofReal, map_div₀, map_mul, map_ofNat,
      Complex.conj_I, Complex.conj_natCast]
    rw [div_mul_div_comm, hsq, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hterm k, ← Finset.sum_div,
    sum_exp_eq n hn (((l : ℕ) : ℤ) - ((j : ℕ) : ℤ))]
  by_cases hjl : j = l
  · subst hjl
    simp [hn0]
  · have hne : ¬ ((n : ℤ) ∣ (((l : ℕ) : ℤ) - ((j : ℕ) : ℤ))) := by
      intro hd
      apply hjl
      have hj := j.isLt
      have hl := l.isLt
      have habs : |(((l : ℕ) : ℤ) - ((j : ℕ) : ℤ))| < (n : ℤ) := by
        rw [abs_lt]
        constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd hd habs
      exact Fin.ext (by omega)
    rw [if_neg hne, if_neg hjl, zero_div]

/-- The 7-qubit quantum Fourier transform matrix (of size `2^7 = 128`) is unitary. -/
theorem qft_unitary_7 : qft (2 ^ 7) ∈ Matrix.unitaryGroup (Fin (2 ^ 7)) ℂ :=
  Matrix.mem_unitaryGroup_iff'.mpr (qft_conjTranspose_mul (2 ^ 7) (by norm_num))

end QC

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

