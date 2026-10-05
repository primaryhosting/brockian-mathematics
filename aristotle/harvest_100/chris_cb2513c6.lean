import Mathlib
/-!
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The module docstring must follow the `import` line: Lean 4 does not permit any
command, including a module doc comment, to precede the imports of a file.)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace QC

open Complex Matrix Finset

/-- A primitive 32nd root of unity, `exp (2 π i / 32)`. -/
noncomputable def omega5 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 32)

/-- The 5-qubit quantum Fourier transform matrix, of size `2 ^ 5 = 32`:
`F j k = ω ^ (j * k) / √32` with `ω = exp (2 π i / 32)`. -/
noncomputable def qft5 : Matrix (Fin 32) (Fin 32) ℂ :=
  Matrix.of fun j k => omega5 ^ (j.val * k.val) / Real.sqrt 32

theorem isPrimitiveRoot_omega5 : IsPrimitiveRoot omega5 32 := by
  have h := Complex.isPrimitiveRoot_exp 32 (by norm_num)
  simpa [omega5] using h

theorem omega5_pow_32 : omega5 ^ 32 = 1 := isPrimitiveRoot_omega5.pow_eq_one

theorem norm_omega5_pow (m : ℕ) : ‖omega5 ^ m‖ = 1 := by
  have h : ‖omega5‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one omega5_pow_32 (by norm_num)
  simp [norm_pow, h]

theorem omega5_pow_ne_zero (m : ℕ) : omega5 ^ m ≠ 0 := by
  intro h
  have hm := norm_omega5_pow m
  rw [h] at hm
  simp at hm

theorem omega5_pow_pow_32 (m : ℕ) : (omega5 ^ m) ^ 32 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, omega5_pow_32, one_pow]

theorem star_omega5_pow (m : ℕ) : (starRingEnd ℂ) (omega5 ^ m) = (omega5 ^ m)⁻¹ :=
  (Complex.inv_eq_conj (norm_omega5_pow m)).symm

/-- The 5-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_unitary_5 : qft5 ∈ Matrix.unitaryGroup (Fin 32) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext j l
  rw [Matrix.mul_apply]
  have hs : ((Real.sqrt 32 : ℝ) : ℂ) * ((Real.sqrt 32 : ℝ) : ℂ) = 32 := by
    have h : Real.sqrt 32 * Real.sqrt 32 = 32 := Real.mul_self_sqrt (by norm_num)
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h
  set x : ℂ := omega5 ^ j.val * (omega5 ^ l.val)⁻¹ with hx
  have key : ∀ k : Fin 32, qft5 j k * (star qft5) k l = x ^ k.val / 32 := by
    intro k
    simp only [qft5, Matrix.of_apply, Matrix.star_apply, star_def]
    rw [map_div₀, star_omega5_pow, Complex.conj_ofReal, div_mul_div_comm, hs]
    congr 1
    rw [hx, mul_pow, inv_pow, ← pow_mul, ← pow_mul]
  rw [Finset.sum_congr rfl fun k _ => key k, ← Finset.sum_div]
  have hx32 : x ^ 32 = 1 := by
    rw [hx, mul_pow, inv_pow, omega5_pow_pow_32, omega5_pow_pow_32]
    norm_num
  by_cases hjl : j = l
  · subst hjl
    have hxone : x = 1 := by
      rw [hx]
      exact mul_inv_cancel₀ (omega5_pow_ne_zero j.val)
    have hsum : ∑ k : Fin 32, x ^ (k : ℕ) = 32 := by simp [hxone]
    rw [hsum]
    simp
  · have hxne : x ≠ 1 := by
      intro h
      refine hjl (Fin.ext ?_)
      have hj : omega5 ^ j.val = omega5 ^ l.val :=
        (mul_inv_eq_one₀ (omega5_pow_ne_zero l.val)).mp (hx ▸ h)
      exact isPrimitiveRoot_omega5.pow_inj j.isLt l.isLt hj
    have hsum : ∑ k : Fin 32, x ^ (k : ℕ) = 0 := by
      have hgeom : ∑ k ∈ Finset.range 32, x ^ k = (x ^ 32 - 1) / (x - 1) :=
        geom_sum_eq hxne 32
      rw [hx32, sub_self, zero_div] at hgeom
      rw [← hgeom]
      exact (Finset.sum_range fun k => x ^ k).symm
    rw [hsum]
    simp [hjl]

end QC

