/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

open Complex Finset Matrix

/-- The `N × N` discrete Fourier transform (quantum Fourier transform) matrix:
`F i j = exp (2 π i · j / N) / √N`. -/

private lemma root_sum (N : ℕ) (hN : 0 < N) (m : ℤ) (hm : m.natAbs < N) :
    ∑ k : Fin N, Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) * (m : ℂ)) / N)
      = if m = 0 then (N : ℂ) else 0 := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / N) with hζ
  have hsum : ∑ k : Fin N, Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) * (m : ℂ)) / N)
      = ∑ k ∈ Finset.range N, ζ ^ k := by
    rw [Fin.sum_univ_eq_sum_range
      (fun k => Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) * (m : ℂ)) / N))]
    exact Finset.sum_congr rfl (fun k _ => (exp_root_pow N (m : ℂ) k).symm)
  rw [hsum]
  by_cases h0 : m = 0
  · subst h0
    simp [hζ]
  · rw [if_neg h0]
    have hζN : ζ ^ N = 1 := by
      rw [hζ, exp_root_pow]
      have h : (2 : ℂ) * Real.pi * Complex.I * ((N : ℂ) * (m : ℂ)) / N
          = (m : ℂ) * (2 * Real.pi * Complex.I) := by field_simp
      rw [h, Complex.exp_int_mul_two_pi_mul_I]
    have hζ1 : ζ ≠ 1 := by
      intro hc
      rw [hζ, Complex.exp_eq_one_iff] at hc
      obtain ⟨n, hn⟩ := hc
      field_simp at hn
      have hmz : m = N * n := by exact_mod_cast hn
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp at hmz
        exact h0 hmz
      have hnat : m.natAbs = N * n.natAbs := by
        rw [hmz, Int.natAbs_mul]; simp
      have : N ≤ m.natAbs := by
        rw [hnat]
        exact Nat.le_mul_of_pos_right N (Int.natAbs_pos.mpr hn0)
      omega
    rw [geom_sum_eq hζ1, hζN]
    simp

/-- The `(i, k)`-entry of `Fᴴ` times the `(k, j)`-entry of `F`. -/
