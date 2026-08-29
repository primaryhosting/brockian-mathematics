import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Matrix

namespace Chem

/-- The primitive 9-th root of unity `exp (2πi/9)`. -/

lemma root_of_unity_of_eigen {v : Fin 9 → ℂ} {μ z : ℂ} (hv0 : v ≠ 0)
    (hv : ∀ i : Fin 9, v (i - 1) + v (i + 1) = μ * v i) (hz : z ≠ 0) (hz2 : z ^ 2 + 1 = μ * z) :
    z ^ 9 = 1 := by
  have e0 : v 8 + v 1 = μ * v 0 := by simpa using hv 0
  have e1 : v 0 + v 2 = μ * v 1 := by simpa using hv 1
  have e2 : v 1 + v 3 = μ * v 2 := by simpa using hv 2
  have e3 : v 2 + v 4 = μ * v 3 := by simpa using hv 3
  have e4 : v 3 + v 5 = μ * v 4 := by simpa using hv 4
  have e5 : v 4 + v 6 = μ * v 5 := by simpa using hv 5
  have e6 : v 5 + v 7 = μ * v 6 := by simpa using hv 6
  have e7 : v 6 + v 8 = μ * v 7 := by simpa using hv 7
  have e8 : v 7 + v 0 = μ * v 8 := by simpa using hv 8
  -- the "shifted" quantities `u i = v (i+1) - z * v i` satisfy `u i = z * u (i+1)`
  have h0 : v 1 - z * v 0 = z * (v 2 - z * v 1) := by linear_combination (-z) * e1 + v 1 * hz2
  have h1 : v 2 - z * v 1 = z * (v 3 - z * v 2) := by linear_combination (-z) * e2 + v 2 * hz2
  have h2 : v 3 - z * v 2 = z * (v 4 - z * v 3) := by linear_combination (-z) * e3 + v 3 * hz2
  have h3 : v 4 - z * v 3 = z * (v 5 - z * v 4) := by linear_combination (-z) * e4 + v 4 * hz2
  have h4 : v 5 - z * v 4 = z * (v 6 - z * v 5) := by linear_combination (-z) * e5 + v 5 * hz2
  have h5 : v 6 - z * v 5 = z * (v 7 - z * v 6) := by linear_combination (-z) * e6 + v 6 * hz2
  have h6 : v 7 - z * v 6 = z * (v 8 - z * v 7) := by linear_combination (-z) * e7 + v 7 * hz2
  have h7 : v 8 - z * v 7 = z * (v 0 - z * v 8) := by linear_combination (-z) * e8 + v 8 * hz2
  have h8 : v 0 - z * v 8 = z * (v 1 - z * v 0) := by linear_combination (-z) * e0 + v 0 * hz2
  by_contra hne
  -- if `z ^ 9 ≠ 1` all the `u i` vanish
  have hcycle : v 1 - z * v 0 = z ^ 9 * (v 1 - z * v 0) := by
    linear_combination h0 + z * h1 + z ^ 2 * h2 + z ^ 3 * h3 + z ^ 4 * h4 + z ^ 5 * h5 +
      z ^ 6 * h6 + z ^ 7 * h7 + z ^ 8 * h8
  have hu0 : v 1 - z * v 0 = 0 := by
    have : (z ^ 9 - 1) * (v 1 - z * v 0) = 0 := by linear_combination -hcycle
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  have hu1 : v 2 - z * v 1 = 0 := by
    have := h0; rw [hu0] at this; exact (mul_eq_zero.1 this.symm).resolve_left hz
  have hu2 : v 3 - z * v 2 = 0 := by
    have := h1; rw [hu1] at this; exact (mul_eq_zero.1 this.symm).resolve_left hz
  have hu3 : v 4 - z * v 3 = 0 := by
    have := h2; rw [hu2] at this; exact (mul_eq_zero.1 this.symm).resolve_left hz
  have hu4 : v 5 - z * v 4 = 0 := by
    have := h3; rw [hu3] at this; exact (mul_eq_zero.1 this.symm).resolve_left hz
  have hu5 : v 6 - z * v 5 = 0 := by
    have := h4; rw [hu4] at this; exact (mul_eq_zero.1 this.symm).resolve_left hz
  have hu6 : v 7 - z * v 6 = 0 := by
    have := h5; rw [hu5] at this; exact (mul_eq_zero.1 this.symm).resolve_left hz
  have hu7 : v 8 - z * v 7 = 0 := by
    have := h6; rw [hu6] at this; exact (mul_eq_zero.1 this.symm).resolve_left hz
  have hu8 : v 0 - z * v 8 = 0 := by
    have := h7; rw [hu7] at this; exact (mul_eq_zero.1 this.symm).resolve_left hz
  -- hence `v 0 = z ^ 9 * v 0`, forcing `v = 0`
  have hv00 : v 0 = 0 := by
    have hcyc : v 0 = z ^ 9 * v 0 := by
      have := sub_eq_zero.1 hu8
      linear_combination this + z * sub_eq_zero.1 hu7 + z ^ 2 * sub_eq_zero.1 hu6 +
        z ^ 3 * sub_eq_zero.1 hu5 + z ^ 4 * sub_eq_zero.1 hu4 + z ^ 5 * sub_eq_zero.1 hu3 +
        z ^ 6 * sub_eq_zero.1 hu2 + z ^ 7 * sub_eq_zero.1 hu1 + z ^ 8 * sub_eq_zero.1 hu0
    have : (z ^ 9 - 1) * v 0 = 0 := by linear_combination -hcyc
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  apply hv0
  funext i
  have h1' : v 1 = 0 := by have := sub_eq_zero.1 hu0; rw [this, hv00, mul_zero]
  have h2' : v 2 = 0 := by have := sub_eq_zero.1 hu1; rw [this, h1', mul_zero]
  have h3' : v 3 = 0 := by have := sub_eq_zero.1 hu2; rw [this, h2', mul_zero]
  have h4' : v 4 = 0 := by have := sub_eq_zero.1 hu3; rw [this, h3', mul_zero]
  have h5' : v 5 = 0 := by have := sub_eq_zero.1 hu4; rw [this, h4', mul_zero]
  have h6' : v 6 = 0 := by have := sub_eq_zero.1 hu5; rw [this, h5', mul_zero]
  have h7' : v 7 = 0 := by have := sub_eq_zero.1 hu6; rw [this, h6', mul_zero]
  have h8' : v 8 = 0 := by have := sub_eq_zero.1 hu7; rw [this, h7', mul_zero]
  fin_cases i <;> simp_all

/-- **Hückel theory for the C₉ ring.**  A complex number `μ` is an eigenvalue of the adjacency
matrix of the cycle graph `C₉` if and only if `μ = 2 cos (2πk/9)` for some `k = 0, …, 8`. -/
