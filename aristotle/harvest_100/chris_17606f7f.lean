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

/-- The primitive 8-th root of unity raised to an integer power `d`,
written as `exp (2 π i d / 8)`. -/
noncomputable def zeta8 (d : ℤ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / 8)

/-- The 3-qubit quantum Fourier transform matrix, of size `8 × 8`. -/
noncomputable def qft3 : Matrix (Fin 8) (Fin 8) ℂ :=
  fun j k => zeta8 ((j : ℤ) * (k : ℤ)) / (Real.sqrt 8 : ℝ)

lemma zeta8_eq_one_iff (d : ℤ) : zeta8 d = 1 ↔ (8 : ℤ) ∣ d := by
  rw [zeta8, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have h : (d : ℂ) = ((8 * n : ℤ) : ℂ) := by
      push_cast
      field_simp at hn
      linear_combination hn
    exact_mod_cast h
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

lemma zeta8_pow (d : ℤ) (n : ℕ) : zeta8 d ^ n = zeta8 (n * d) := by
  rw [zeta8, zeta8, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma zeta8_sum (d : ℤ) :
    ∑ n : Fin 8, zeta8 ((n : ℤ) * d) = if (8 : ℤ) ∣ d then 8 else 0 := by
  by_cases hd : (8 : ℤ) ∣ d
  · simp only [hd, if_true]
    have h1 : ∀ n : Fin 8, zeta8 ((n : ℤ) * d) = 1 := by
      intro n
      rw [← zeta8_pow d (n : ℕ)]
      · rw [(zeta8_eq_one_iff d).mpr hd, one_pow]
    simp [h1]
  · simp only [hd, if_false]
    have hz : zeta8 d ≠ 1 := fun h => hd ((zeta8_eq_one_iff d).mp h)
    have h8 : zeta8 d ^ 8 = 1 := by
      rw [zeta8_pow]
      exact (zeta8_eq_one_iff _).mpr ⟨d, by push_cast; ring⟩
    have hsum : ∑ n : Fin 8, zeta8 ((n : ℤ) * d) = ∑ i ∈ Finset.range 8, zeta8 d ^ i := by
      rw [Fin.sum_univ_eq_sum_range (fun i => zeta8 ((i : ℤ) * d))]
      · refine Finset.sum_congr rfl ?_
        intro i _
        rw [zeta8_pow]
    rw [hsum, geom_sum_eq hz, h8]
    simp

theorem qft_unitary_3 : qft3 ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext j k
  rw [Matrix.mul_apply]
  have hs8 : ((Real.sqrt 8 : ℝ) : ℂ) * ((Real.sqrt 8 : ℝ) : ℂ) = 8 := by
    have : (Real.sqrt 8) * (Real.sqrt 8) = 8 := Real.mul_self_sqrt (by norm_num)
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this
  have key : ∀ n : Fin 8,
      qft3 j n * (star qft3) n k = zeta8 ((n : ℤ) * ((j : ℤ) - (k : ℤ))) / 8 := by
    intro n
    have hstar : (star qft3) n k = (starRingEnd ℂ) (qft3 k n) := rfl
    rw [hstar, qft3, qft3]
    have hconj : (starRingEnd ℂ) (zeta8 ((k : ℤ) * (n : ℤ)) / ((Real.sqrt 8 : ℝ) : ℂ))
        = zeta8 (-((k : ℤ) * (n : ℤ))) / ((Real.sqrt 8 : ℝ) : ℂ) := by
      rw [map_div₀, Complex.conj_ofReal, zeta8, zeta8, ← Complex.exp_conj]
      congr 2
      simp only [map_div₀, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal, map_intCast]
      push_cast
      ring
    rw [hconj]
    have hmul : zeta8 ((j : ℤ) * (n : ℤ)) * zeta8 (-((k : ℤ) * (n : ℤ)))
        = zeta8 ((n : ℤ) * ((j : ℤ) - (k : ℤ))) := by
      rw [zeta8, zeta8, zeta8, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    field_simp
    rw [← hmul]
    have hs8' : ((Real.sqrt 8 : ℝ) : ℂ) ^ 2 = 8 := by rw [pow_two, hs8]
    ring_nf
    rw [hs8']
  rw [Finset.sum_congr rfl (fun n _ => key n)]
  rw [← Finset.sum_div, zeta8_sum]
  by_cases hjk : j = k
  · subst hjk
    simp
  · have hne : ¬ (8 : ℤ) ∣ ((j : ℤ) - (k : ℤ)) := by
      intro h
      apply hjk
      have hj : (j : ℤ) < 8 := by exact_mod_cast j.isLt
      have hk : (k : ℤ) < 8 := by exact_mod_cast k.isLt
      have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg _
      have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg _
      have : (j : ℤ) = (k : ℤ) := by omega
      have : (j : ℕ) = (k : ℕ) := by exact_mod_cast this
      exact Fin.ext this
    simp [hne, hjk]

end QC


