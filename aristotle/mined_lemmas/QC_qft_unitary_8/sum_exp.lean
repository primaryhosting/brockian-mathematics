/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
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

namespace QC

/-- The `N × N` discrete Fourier transform (quantum Fourier transform) matrix, whose
`(j, k)` entry is `exp(2πi·jk/N) / √N`. -/

theorem sum_exp (N : ℕ) (hN : 0 < N) (m : ℤ) :
    ∑ i ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * ((i : ℂ) * (m : ℂ)) / N)
      = if (N : ℤ) ∣ m then (N : ℂ) else 0 := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / N) with hz
  have hterm : ∀ i : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * ((i : ℂ) * (m : ℂ)) / N) = z ^ i := by
    intro i
    rw [hz, ← Complex.exp_nat_mul]
    ring_nf
  simp only [hterm]
  have hzone : z = 1 ↔ (N : ℤ) ∣ m := by
    rw [hz, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      field_simp at hn
      exact_mod_cast hn
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      subst hc
      push_cast
      field_simp
  by_cases h : (N : ℤ) ∣ m
  · simp [h, hzone.mpr h]
  · rw [if_neg h]
    have hz1 : z ≠ 1 := fun hh => h (hzone.mp hh)
    rw [geom_sum_eq hz1, show z ^ N = 1 from by
      rw [hz, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]; exact ⟨m, by field_simp⟩]
    simp

/-- The `N × N` quantum Fourier transform matrix is unitary for every `N > 0`. -/
