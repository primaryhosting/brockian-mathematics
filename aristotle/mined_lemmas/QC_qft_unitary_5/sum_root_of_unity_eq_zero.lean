/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

/-- The `N × N` discrete Fourier transform (quantum Fourier transform) matrix:
its `(j, k)` entry is `exp (2 π i j k / N) / √N`. -/

lemma sum_root_of_unity_eq_zero (N : ℕ) (hN : 0 < N) (j l : Fin N) (hjl : j ≠ l) :
    ∑ k : Fin N, (Complex.exp (2 * Real.pi * Complex.I * ((l : ℕ) - (j : ℕ)) / N)) ^ (k : ℕ)
      = 0 := by
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((l : ℕ) - (j : ℕ)) / N) with hz
  have hzN : z ^ N = 1 := by
    rw [hz, ← Complex.exp_nat_mul]
    have h : (N : ℂ) * (2 * Real.pi * Complex.I * ((l : ℕ) - (j : ℕ)) / N)
        = (((l : ℤ) - (j : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hz1 : z ≠ 1 := by
    intro h
    rw [hz, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    field_simp at hn
    have keyZ : (l : ℤ) - (j : ℤ) = N * n := by exact_mod_cast hn
    have hdvd : (N : ℤ) ∣ ((l : ℤ) - (j : ℤ)) := ⟨n, keyZ⟩
    have habs : |((l : ℤ) - (j : ℤ))| < (N : ℤ) := by
      have h1 : (l : ℤ) < N := by exact_mod_cast l.isLt
      have h2 : (j : ℤ) < N := by exact_mod_cast j.isLt
      have h3 : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg _
      have h4 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg _
      rw [abs_lt]; omega
    have hzero := Int.eq_zero_of_abs_lt_dvd hdvd habs
    exact hjl (Fin.ext (by omega)).symm
  rw [Fin.sum_univ_eq_sum_range (fun k => z ^ k), geom_sum_eq hz1, hzN, sub_self, zero_div]

/-- The DFT matrix satisfies `Qᴴ * Q = 1`. -/
