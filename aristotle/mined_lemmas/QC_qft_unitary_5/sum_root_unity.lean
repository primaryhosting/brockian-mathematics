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

/-- The `N`-dimensional quantum Fourier transform matrix:
`(QFT_N)_{j,k} = exp(2πi·jk/N) / √N`. -/

lemma sum_root_unity (N : ℕ) (hN : 0 < N) (d : ℤ) :
    ∑ k : Fin N, Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) * d) / N)
      = if (N : ℤ) ∣ d then (N : ℂ) else 0 := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = 2 * Real.pi * Complex.I * d / N := ⟨_, rfl⟩
  have hterm : ∀ k : Fin N, Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) * d) / N)
      = Complex.exp z ^ (k : ℕ) := by
    intro k
    rw [← Complex.exp_nat_mul]
    congr 1
    rw [hz]
    field_simp
  rw [Finset.sum_congr rfl (fun k _ => hterm k),
    ← Finset.sum_range fun i => Complex.exp z ^ i]
  have hzone : Complex.exp z = 1 ↔ (N : ℤ) ∣ d := by
    rw [Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      rw [hz] at hn
      field_simp at hn
      exact ⟨n, by exact_mod_cast hn⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rw [hz, hn]
      push_cast
      field_simp
  by_cases h : (N : ℤ) ∣ d
  · simp [h, hzone.2 h, Finset.sum_const]
  · rw [if_neg h]
    have hne : Complex.exp z ≠ 1 := fun hc => h (hzone.1 hc)
    rw [geom_sum_eq hne]
    have hpow : Complex.exp z ^ N = 1 := by
      rw [← Complex.exp_nat_mul]
      have he : (N : ℂ) * z = (d : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hz]; field_simp
      rw [he]
      exact_mod_cast Complex.exp_int_mul_two_pi_mul_I d
    rw [hpow]
    simp

/-- The `N`-dimensional QFT matrix is unitary for every `N > 0`. -/
