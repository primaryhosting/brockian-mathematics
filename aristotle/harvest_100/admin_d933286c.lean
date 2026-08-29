/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Finset Matrix

/-- The primitive `n`-th root of unity `exp (2 π i / n)` used in the QFT. -/
noncomputable def qftOmega (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The `n`-dimensional quantum Fourier transform matrix,
`F j k = ω ^ (j * k) / √n` with `ω = exp (2 π i / n)`. -/
noncomputable def qftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => qftOmega n ^ ((j : ℕ) * (k : ℕ)) / (Real.sqrt n : ℂ)

lemma qftOmega_isPrimitiveRoot {n : ℕ} (hn : n ≠ 0) :
    IsPrimitiveRoot (qftOmega n) n :=
  Complex.isPrimitiveRoot_exp n hn

lemma conj_qftOmega (n : ℕ) :
    (starRingEnd ℂ) (qftOmega n) = (qftOmega n)⁻¹ := by
  have h : (2 : ℂ) * Real.pi * Complex.I / n = ((2 * Real.pi / n : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hnorm : ‖qftOmega n‖ = 1 := by
    rw [qftOmega, h, Complex.norm_exp_ofReal_mul_I]
  exact (Complex.inv_eq_conj hnorm).symm

/-- Orthogonality of the columns of the (unnormalized) QFT matrix. -/
lemma sum_qftOmega {n : ℕ} (hn : n ≠ 0) (j k : Fin n) :
    ∑ l : Fin n, (starRingEnd ℂ) (qftOmega n ^ ((l : ℕ) * (j : ℕ)))
        * qftOmega n ^ ((l : ℕ) * (k : ℕ)) = if j = k then (n : ℂ) else 0 := by
  set ζ := qftOmega n with hζdef
  have hprim : IsPrimitiveRoot ζ n := qftOmega_isPrimitiveRoot hn
  have hζ0 : ζ ≠ 0 := by
    intro h
    have h1 := hprim.pow_eq_one
    rw [h, zero_pow hn] at h1
    exact zero_ne_one h1
  set x : ℂ := ζ ^ ((k : ℤ) - (j : ℤ)) with hx
  have hterm : ∀ l : Fin n, (starRingEnd ℂ) (ζ ^ ((l : ℕ) * (j : ℕ)))
      * ζ ^ ((l : ℕ) * (k : ℕ)) = x ^ (l : ℕ) := by
    intro l
    have h1 : (starRingEnd ℂ) (ζ ^ ((l : ℕ) * (j : ℕ)))
        = ζ ^ (-(((l : ℕ) * (j : ℕ) : ℕ) : ℤ)) := by
      rw [map_pow, conj_qftOmega, ← hζdef, _root_.zpow_neg, zpow_natCast, inv_pow]
    have h2 : ζ ^ ((l : ℕ) * (k : ℕ)) = ζ ^ ((((l : ℕ) * (k : ℕ) : ℕ)) : ℤ) :=
      (zpow_natCast _ _).symm
    rw [h1, h2, ← zpow_add₀ hζ0, hx, ← zpow_natCast (ζ ^ ((k : ℤ) - (j : ℤ))) (l : ℕ),
      ← _root_.zpow_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun l _ => hterm l), Fin.sum_univ_eq_sum_range (fun l => x ^ l) n]
  by_cases hjk : j = k
  · have hx1 : x = 1 := by simp [hx, hjk]
    simp [hx1, hjk]
  · have hdvd : ¬ ((n : ℤ) ∣ ((k : ℤ) - (j : ℤ))) := by
      intro hd
      have habs : |((k : ℤ) - (j : ℤ))| < (n : ℤ) := by
        have hj := j.isLt
        have hk := k.isLt
        rw [abs_lt]
        constructor <;> omega
      have hzero := Int.eq_zero_of_abs_lt_dvd hd habs
      have hnat : (j : ℕ) = (k : ℕ) := by omega
      exact hjk (Fin.ext hnat)
    have hx1 : x ≠ 1 := by
      rw [hx]
      exact fun h => hdvd ((hprim.zpow_eq_one_iff_dvd _).mp h)
    have hxn : x ^ n = 1 := by
      rw [hx, ← zpow_natCast (ζ ^ ((k : ℤ) - (j : ℤ))) n, ← _root_.zpow_mul, mul_comm,
        _root_.zpow_mul, zpow_natCast, hprim.pow_eq_one, _root_.one_zpow]
    rw [geom_sum_eq hx1, hxn, sub_self, zero_div, if_neg hjk]

/-- The 5-qubit (32-dimensional) quantum Fourier transform matrix is unitary. -/
theorem qft_unitary_5 : qftMatrix 32 ∈ Matrix.unitaryGroup (Fin 32) ℂ := by
  have hsqrt : ((Real.sqrt ((32 : ℕ) : ℝ) : ℝ) : ℂ) * ((Real.sqrt ((32 : ℕ) : ℝ) : ℝ) : ℂ)
      = (32 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    norm_num
  have key : (qftMatrix 32)ᴴ * qftMatrix 32 = 1 := by
    ext j k
    rw [Matrix.mul_apply]
    have hentry : ∀ l : Fin 32, (qftMatrix 32)ᴴ j l * qftMatrix 32 l k
        = ((starRingEnd ℂ) (qftOmega 32 ^ ((l : ℕ) * (j : ℕ)))
            * qftOmega 32 ^ ((l : ℕ) * (k : ℕ))) / (32 : ℂ) := by
      intro l
      simp only [Matrix.conjTranspose_apply, qftMatrix, Complex.star_def, map_div₀,
        Complex.conj_ofReal]
      rw [div_mul_div_comm, hsqrt]
    rw [Finset.sum_congr rfl (fun l _ => hentry l), ← Finset.sum_div,
      sum_qftOmega (by norm_num) j k, Matrix.one_apply]
    by_cases h : j = k <;> simp [h]
  rw [Matrix.mem_unitaryGroup_iff']
  simpa using key

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

