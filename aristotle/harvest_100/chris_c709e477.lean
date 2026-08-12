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

/-- The primitive `128`-th root of unity `exp (2 π i / 128)` used by the 7-qubit QFT. -/
noncomputable def omega7 : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (128 : ℕ))

/-- The 7-qubit quantum Fourier transform matrix, acting on the `2 ^ 7 = 128`
dimensional state space: its `(j, k)` entry is `exp (2 π i j k / 128) / √128`. -/
noncomputable def qft7 : Matrix (Fin 128) (Fin 128) ℂ :=
  Matrix.of fun j k => omega7 ^ ((j : ℕ) * (k : ℕ)) / (Real.sqrt 128 : ℝ)

theorem omega7_isPrimitiveRoot : IsPrimitiveRoot omega7 128 :=
  Complex.isPrimitiveRoot_exp 128 (by norm_num)

theorem omega7_pow_128 : omega7 ^ (128 : ℕ) = 1 := omega7_isPrimitiveRoot.pow_eq_one

theorem omega7_ne_zero : omega7 ≠ 0 := Complex.exp_ne_zero _

theorem norm_omega7 : ‖omega7‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one omega7_pow_128 (by norm_num)

/-- The conjugate of a power of `omega7` is the inverse power. -/
theorem conj_omega7_pow (m : ℕ) :
    (starRingEnd ℂ) (omega7 ^ m) = (omega7 ^ m)⁻¹ := by
  rw [Complex.inv_eq_conj]
  rw [norm_pow, norm_omega7, one_pow]

/-- Key orthogonality: the geometric sum of `z ^ l` over `l < 128`, where `z` is a
power of `omega7`, is `128` if `z = 1` and `0` otherwise. -/
theorem geom_sum_omega7 (d : ℤ) :
    ∑ l ∈ Finset.range 128, (omega7 ^ d) ^ l = if (128 : ℤ) ∣ d then 128 else 0 := by
  by_cases h : (128 : ℤ) ∣ d
  · have hz : omega7 ^ d = 1 := (omega7_isPrimitiveRoot.zpow_eq_one_iff_dvd d).2 h
    simp [hz, h]
  · have hz : omega7 ^ d ≠ 1 := fun hz =>
      h ((omega7_isPrimitiveRoot.zpow_eq_one_iff_dvd d).1 hz)
    rw [geom_sum_eq hz, if_neg h]
    have h128 : (omega7 ^ d) ^ (128 : ℕ) = 1 := by
      rw [← zpow_natCast (omega7 ^ d) 128, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, omega7_pow_128, one_zpow]
    rw [h128, sub_self, zero_div]

/-- The 7-qubit QFT matrix is unitary. -/
theorem qft_unitary_7 : qft7 ∈ Matrix.unitaryGroup (Fin 128) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hs : (0:ℝ) ≤ 128 := by norm_num
  have hsq : (Real.sqrt 128 : ℝ) ^ 2 = 128 := Real.sq_sqrt hs
  have hsne : (Real.sqrt 128 : ℝ) ≠ 0 := by
    have : (0:ℝ) < Real.sqrt 128 := Real.sqrt_pos.2 (by norm_num)
    exact ne_of_gt this
  have hsC : ((Real.sqrt 128 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsne
  ext j k
  rw [Matrix.mul_apply]
  have hterm : ∀ l : Fin 128,
      qft7 j l * (star qft7) l k
        = (((Real.sqrt 128 : ℝ) : ℂ) ^ 2)⁻¹ *
            (omega7 ^ ((j : ℤ) - (k : ℤ))) ^ (l : ℕ) := by
    intro l
    have hstar : (star qft7) l k = (starRingEnd ℂ) (qft7 k l) := rfl
    rw [hstar]
    simp only [qft7, Matrix.of_apply, map_div₀, Complex.conj_ofReal, conj_omega7_pow]
    have hj : omega7 ^ ((j : ℕ) * (l : ℕ)) = (omega7 ^ (j : ℤ)) ^ (l : ℕ) := by
      rw [← zpow_natCast omega7 ((j:ℕ) * (l:ℕ)), ← zpow_natCast (omega7 ^ (j:ℤ)) (l:ℕ),
        ← zpow_mul]
      norm_cast
    have hk : (omega7 ^ ((k : ℕ) * (l : ℕ)))⁻¹ = (omega7 ^ (-(k : ℤ))) ^ (l : ℕ) := by
      rw [← zpow_natCast omega7 ((k:ℕ) * (l:ℕ)), ← zpow_neg,
        ← zpow_natCast (omega7 ^ (-(k:ℤ))) (l:ℕ), ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [hj, hk]
    have hsplit : (omega7 ^ ((j : ℤ) - (k : ℤ))) ^ (l : ℕ)
        = (omega7 ^ (j : ℤ)) ^ (l : ℕ) * (omega7 ^ (-(k : ℤ))) ^ (l : ℕ) := by
      rw [← mul_pow, ← zpow_add₀ omega7_ne_zero]
      ring_nf
    rw [hsplit]
    field_simp
  rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Finset.mul_sum]
  have hsum : ∑ l : Fin 128, (omega7 ^ ((j : ℤ) - (k : ℤ))) ^ (l : ℕ)
      = ∑ l ∈ Finset.range 128, (omega7 ^ ((j : ℤ) - (k : ℤ))) ^ l := by
    rw [Finset.sum_range fun l => (omega7 ^ ((j : ℤ) - (k : ℤ))) ^ l]
  rw [hsum, geom_sum_omega7]
  have hdvd : ((128 : ℤ) ∣ ((j : ℤ) - (k : ℤ))) ↔ j = k := by
    constructor
    · intro h
      have hj : (j : ℕ) < 128 := j.isLt
      have hk : (k : ℕ) < 128 := k.isLt
      have : (j : ℤ) = (k : ℤ) := by omega
      have : (j : ℕ) = (k : ℕ) := by exact_mod_cast this
      exact Fin.ext this
    · intro h; simp [h]
  have hcast : (((Real.sqrt 128 : ℝ) : ℂ) ^ 2) = (128 : ℂ) := by
    rw [← Complex.ofReal_pow, hsq]
    norm_cast
  by_cases h : j = k
  · subst h
    rw [if_pos (hdvd.2 rfl), hcast, Matrix.one_apply_eq]
    exact inv_mul_cancel₀ (by norm_num)
  · rw [if_neg (fun hd => h (hdvd.1 hd)), Matrix.one_apply_ne h, mul_zero]

/-- Explicit form of unitarity: `qft7 * qft7ᴴ = 1`. -/
theorem qft7_mul_conjTranspose : qft7 * Matrix.conjTranspose qft7 = 1 :=
  Matrix.mem_unitaryGroup_iff.mp qft_unitary_7

/-- Explicit form of unitarity: `qft7ᴴ * qft7 = 1`. -/
theorem qft7_conjTranspose_mul : Matrix.conjTranspose qft7 * qft7 = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp qft_unitary_7

end QC

