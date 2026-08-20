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

theorem qft_unitary (N : ℕ) (hN : 0 < N) : qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsq : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  have hstar : ∀ a : ℕ,
      star (Complex.exp (2 * Real.pi * Complex.I * (a : ℕ) / N) / ((Real.sqrt N : ℝ) : ℂ))
        = Complex.exp (-(2 * Real.pi * Complex.I * (a : ℕ) / N)) / ((Real.sqrt N : ℝ) : ℂ) := by
    intro a
    simp [Complex.conj_ofReal, ← Complex.exp_conj, map_ofNat]
    ring_nf
  rw [Matrix.mem_unitaryGroup_iff']
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hkey : ∀ k : Fin N, (star (qftMatrix N)) j k * qftMatrix N k l
      = (1 / (N : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) * ((l : ℕ) - (j : ℕ) : ℤ)) / N) := by
    intro k
    rw [Matrix.star_apply, qftMatrix]
    simp only [Matrix.of_apply]
    rw [hstar ((k : ℕ) * (j : ℕ)), div_mul_div_comm, ← Complex.exp_add, hsq, one_div,
      ← div_eq_inv_mul]
    congr 1
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl (fun k _ => hkey k), ← Finset.mul_sum,
    sum_root_unity N hN ((l : ℕ) - (j : ℕ) : ℤ)]
  by_cases h : j = l
  · subst h
    simp [hN0]
  · have hne : ((l : ℕ) : ℤ) - (j : ℕ) ≠ 0 := by
      simp only [sub_ne_zero]
      intro hc
      exact h (Fin.ext (by exact_mod_cast hc.symm))
    have hnd : ¬ ((N : ℤ) ∣ ((l : ℕ) - (j : ℕ) : ℤ)) := by
      intro hd
      refine hne (Int.eq_zero_of_abs_lt_dvd hd ?_)
      have h1 := j.isLt
      have h2 := l.isLt
      rw [abs_lt]
      omega
    rw [if_neg hnd, if_neg h]
    ring

/-- The 5-qubit QFT matrix (dimension `2^5 = 32`) is unitary. -/
