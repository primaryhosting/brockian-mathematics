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

