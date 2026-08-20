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

open Complex

/-- The `N × N` discrete Fourier transform matrix:
`(dftMatrix N) j k = (1/√N) * exp (2πi jk / N)`. -/

lemma sum_zetaN_pow {N : ℕ} (hN : 0 < N) (j l : Fin N) :
    ∑ k : Fin N, (zetaN N) ^ ((j : ℕ) * (k : ℕ)) * ((zetaN N) ^ ((l : ℕ) * (k : ℕ)))⁻¹
      = if j = l then (N : ℂ) else 0 := by
  set z := zetaN N with hz
  have hprim : IsPrimitiveRoot z N := isPrimitiveRoot_zetaN hN
  have hz0 : z ≠ 0 := zetaN_ne_zero
  set w : ℂ := z ^ ((j : ℤ) - (l : ℤ)) with hw
  have hterm : ∀ k : Fin N,
      z ^ ((j : ℕ) * (k : ℕ)) * (z ^ ((l : ℕ) * (k : ℕ)))⁻¹ = w ^ (k : ℕ) := by
    intro k
    rw [hw, ← zpow_natCast z ((j : ℕ) * (k : ℕ)), ← zpow_natCast z ((l : ℕ) * (k : ℕ)),
      ← zpow_neg, ← zpow_add₀ hz0, ← zpow_natCast (z ^ ((j : ℤ) - (l : ℤ))) (k : ℕ),
      ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  by_cases hjl : j = l
  · have hw1 : w = 1 := by
      rw [hw, hjl]
      simp
    simp [hw1, hjl]
  · have hwne : w ≠ 1 := by
      intro hw1
      have hdvd : ((N : ℕ) : ℤ) ∣ ((j : ℕ) : ℤ) - ((l : ℕ) : ℤ) :=
        (hprim.zpow_eq_one_iff_dvd _).mp (hw ▸ hw1)
      have hlt : |((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)| < (N : ℤ) := by
        have hj := j.isLt
        have hl := l.isLt
        rw [abs_lt]
        omega
      have h1 : ((j : ℕ) : ℤ) - ((l : ℕ) : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
      apply hjl
      have : (j : ℕ) = (l : ℕ) := by omega
      exact Fin.ext this
    have hsum : ∑ k : Fin N, w ^ (k : ℕ) = ∑ k ∈ Finset.range N, w ^ k := by
      rw [Fin.sum_univ_eq_sum_range (fun k => w ^ k)]
    rw [hsum, geom_sum_eq hwne]
    have hwN : w ^ N = 1 := by
      rw [hw, ← zpow_natCast (z ^ ((j : ℤ) - (l : ℤ))) N, ← zpow_mul, mul_comm,
        zpow_mul, zpow_natCast, hprim.pow_eq_one, one_zpow]
    rw [hwN]
    simp [hjl]

/-- The DFT matrix is unitary. -/
