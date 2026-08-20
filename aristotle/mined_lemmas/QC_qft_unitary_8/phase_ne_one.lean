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

namespace QC

/-- The `N × N` Quantum Fourier Transform matrix:
`(QFT N) j k = exp (2 π i j k / N) / √N`. -/

private lemma phase_ne_one (hN : N ≠ 0) {a b : Fin N} (hab : a ≠ b) : phase N a b ≠ 1 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  intro h
  rw [phase, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hc : ((b : ℕ) : ℂ) - ((a : ℕ) : ℂ) = (n : ℂ) * N := by
    field_simp at hn
    linear_combination hn
  have hz : ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) = n * N := by exact_mod_cast hc
  have h1 : ((a : ℕ) : ℤ) < N := by exact_mod_cast a.isLt
  have h2 : ((b : ℕ) : ℤ) < N := by exact_mod_cast b.isLt
  have h3 : (0 : ℤ) ≤ ((a : ℕ) : ℤ) := Int.natCast_nonneg _
  have h4 : (0 : ℤ) ≤ ((b : ℕ) : ℤ) := Int.natCast_nonneg _
  have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with hlt | heq | hgt
    · nlinarith [Int.lt_iff_add_one_le.mp hlt]
    · exact heq
    · nlinarith [Int.lt_iff_add_one_le.mp hgt]
  rw [hn0, zero_mul] at hz
  have hEq : ((b : ℕ) : ℤ) = ((a : ℕ) : ℤ) := by linarith
  have : (b : ℕ) = (a : ℕ) := by exact_mod_cast hEq
  exact hab (Fin.ext this).symm

