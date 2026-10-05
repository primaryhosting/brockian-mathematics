import Mathlib
/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace QC

/-- The `N × N` quantum Fourier transform matrix:
`(QFT_N) j k = N^(-1/2) * exp (2πi jk / N)`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k =>
    (Real.sqrt N : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * (j : ℕ) * (k : ℕ) / N)

/-- Geometric sum of `N`-th roots of unity. -/
lemma sum_root_of_unity (N : ℕ) (hN : 0 < N) (m : ℤ) :
    ∑ l ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * (m * l) / N)
      = if (N : ℤ) ∣ m then (N : ℂ) else 0 := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * m / N) with hz
  have hterm : ∀ l : ℕ, Complex.exp (2 * Real.pi * Complex.I * (m * l) / N) = z ^ l := by
    intro l
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  rw [Finset.sum_congr rfl (fun l _ => hterm l)]
  by_cases hdvd : (N : ℤ) ∣ m
  · have hz1 : z = 1 := by
      obtain ⟨c, hc⟩ := hdvd
      rw [hz, Complex.exp_eq_one_iff]
      refine ⟨c, ?_⟩
      rw [hc]
      push_cast
      field_simp
    simp [hz1, hdvd]
  · have hzN : z ^ N = 1 := by
      rw [hz, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      refine ⟨m, ?_⟩
      field_simp
    have hz1 : z ≠ 1 := by
      intro h
      rw [hz, Complex.exp_eq_one_iff] at h
      obtain ⟨c, hc⟩ := h
      apply hdvd
      refine ⟨c, ?_⟩
      field_simp at hc
      exact_mod_cast hc
    rw [geom_sum_eq hz1, hzN, sub_self, zero_div]
    simp [hdvd]

/-- The `N × N` QFT matrix is unitary, for any `N > 0`. -/
theorem qftMatrix_mem_unitaryGroup (N : ℕ) (hN : 0 < N) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsq : ((Real.sqrt N : ℂ))⁻¹ * ((Real.sqrt N : ℂ))⁻¹ = ((N : ℂ))⁻¹ := by
    rw [← mul_inv]
    congr 1
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    norm_num
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply, Matrix.one_apply, qftMatrix, Matrix.of_apply]
  have hsum : ∀ l : Fin N,
      star ((Real.sqrt N : ℂ)⁻¹ *
          Complex.exp (2 * Real.pi * Complex.I * (l : ℕ) * (j : ℕ) / N)) *
        ((Real.sqrt N : ℂ)⁻¹ *
          Complex.exp (2 * Real.pi * Complex.I * (l : ℕ) * (k : ℕ) / N))
        = ((N : ℂ))⁻¹ *
          Complex.exp (2 * Real.pi * Complex.I * (((k : ℤ) - (j : ℤ) : ℤ) * (l : ℕ)) / N) := by
    intro l
    have hstar : star ((Real.sqrt N : ℂ)⁻¹ *
        Complex.exp (2 * Real.pi * Complex.I * (l : ℕ) * (j : ℕ) / N))
        = (Real.sqrt N : ℂ)⁻¹ *
          Complex.exp (-(2 * Real.pi * Complex.I * (l : ℕ) * (j : ℕ) / N)) := by
      rw [Complex.star_def, map_mul, ← Complex.exp_conj]
      congr 1
      · simp
      · congr 1
        simp [Complex.ext_iff]
        ring
    rw [hstar]
    rw [show (Real.sqrt N : ℂ)⁻¹ * Complex.exp (-(2 * Real.pi * Complex.I * (l : ℕ) * (j : ℕ) / N)) *
        ((Real.sqrt N : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * (l : ℕ) * (k : ℕ) / N))
        = ((Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹) *
          (Complex.exp (-(2 * Real.pi * Complex.I * (l : ℕ) * (j : ℕ) / N)) *
            Complex.exp (2 * Real.pi * Complex.I * (l : ℕ) * (k : ℕ) / N)) from by ring]
    rw [hsq, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun l _ => hsum l)]
  rw [← Finset.mul_sum]
  rw [show ∑ l : Fin N, Complex.exp
        (2 * Real.pi * Complex.I * (((k : ℤ) - (j : ℤ) : ℤ) * (l : ℕ)) / N)
      = ∑ l ∈ Finset.range N, Complex.exp
        (2 * Real.pi * Complex.I * (((k : ℤ) - (j : ℤ) : ℤ) * (l : ℕ)) / N) from by
    rw [Finset.sum_range fun l => Complex.exp
        (2 * Real.pi * Complex.I * (((k : ℤ) - (j : ℤ) : ℤ) * (l : ℕ)) / N)]]
  rw [sum_root_of_unity N hN ((k : ℤ) - (j : ℤ))]
  have hiff : ((N : ℤ) ∣ ((k : ℤ) - (j : ℤ))) ↔ j = k := by
    constructor
    · intro h
      have hj : (j : ℤ) < N := by exact_mod_cast j.isLt
      have hk : (k : ℤ) < N := by exact_mod_cast k.isLt
      have hj0 : (0 : ℤ) ≤ (j : ℕ) := Int.natCast_nonneg _
      have hk0 : (0 : ℤ) ≤ (k : ℕ) := Int.natCast_nonneg _
      have hzero : (k : ℤ) - (j : ℤ) = 0 := by
        rcases h with ⟨c, hc⟩
        have hc1 : c = 0 := by nlinarith [hc]
        simp [hc1] at hc
        exact hc
      have : (j : ℕ) = (k : ℕ) := by omega
      exact Fin.ext this
    · intro h
      simp [h]
  by_cases h : j = k
  · simp [h, hNC]
  · rw [if_neg h, if_neg (fun hh => h (hiff.mp hh)), mul_zero]

/-- **The 7-qubit QFT matrix is unitary.** -/
theorem qft_unitary_7 : qftMatrix (2 ^ 7) ∈ Matrix.unitaryGroup (Fin (2 ^ 7)) ℂ :=
  qftMatrix_mem_unitaryGroup (2 ^ 7) (by norm_num)

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

