import Mathlib
/-!
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace QC

open Complex Matrix Finset

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/
noncomputable def omegaN (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The `N`-dimensional discrete Fourier transform (QFT) matrix:
`(1 / √N) * ω^(j k)` with `ω = exp (2 π i / N)`. -/
noncomputable def qft (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => omegaN N ^ ((j : ℕ) * (k : ℕ)) / (Real.sqrt N : ℝ)

/-- The QFT matrix on `n` qubits, i.e. the `2^n`-dimensional QFT matrix. -/
noncomputable def qftQubits (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := qft (2 ^ n)

lemma isPrimitiveRoot_omegaN {N : ℕ} (hN : 0 < N) : IsPrimitiveRoot (omegaN N) N := by
  have := Complex.isPrimitiveRoot_exp N hN.ne'
  simpa [omegaN, mul_comm, mul_assoc, mul_left_comm] using this

lemma omegaN_pow_N {N : ℕ} (hN : 0 < N) : omegaN N ^ N = 1 :=
  (isPrimitiveRoot_omegaN hN).pow_eq_one

lemma omegaN_ne_zero (N : ℕ) : omegaN N ≠ 0 := by
  simp [omegaN, Complex.exp_ne_zero]

lemma conj_omegaN (N : ℕ) : (starRingEnd ℂ) (omegaN N) = (omegaN N)⁻¹ := by
  rw [omegaN, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.ext_iff]
  ring

theorem qft_conjTranspose_mul_self {N : ℕ} (hN : 0 < N) : (qft N)ᴴ * qft N = 1 := by
  have hω := isPrimitiveRoot_omegaN hN
  have hω0 := omegaN_ne_zero N
  have hsq : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  have hs0 : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr ?_))
    exact_mod_cast hN
  ext j k
  rw [Matrix.mul_apply]
  have key : ∀ l : Fin N, (qft N)ᴴ j l * qft N l k
      = ((omegaN N)⁻¹ ^ (j : ℕ) * omegaN N ^ (k : ℕ)) ^ (l : ℕ) / (N : ℂ) := by
    intro l
    simp only [Matrix.conjTranspose_apply, qft, Complex.star_def, map_div₀, map_pow,
      conj_omegaN, Complex.conj_ofReal]
    rw [div_mul_div_comm, hsq]
    ring
  rw [Finset.sum_congr rfl (fun l _ => key l)]
  rw [← Finset.sum_div]
  set z : ℂ := (omegaN N)⁻¹ ^ (j : ℕ) * omegaN N ^ (k : ℕ) with hz
  have hzN : z ^ N = 1 := by
    rw [hz, mul_pow, ← pow_mul, ← pow_mul, mul_comm (j : ℕ) N, mul_comm (k : ℕ) N,
      pow_mul, pow_mul, inv_pow, omegaN_pow_N hN]
    simp
  by_cases hjk : j = k
  · subst hjk
    have hz1 : z = 1 := by
      rw [hz, inv_pow]; field_simp
    have : ∑ l : Fin N, z ^ (l : ℕ) = (N : ℂ) := by
      simp [hz1]
    rw [this, div_self (Nat.cast_ne_zero.mpr hN.ne' : (N : ℂ) ≠ 0), Matrix.one_apply_eq]
  · have hzne : z ≠ 1 := by
      intro h
      have h' : (omegaN N ^ (j : ℕ))⁻¹ * omegaN N ^ (k : ℕ) = 1 := by
        rw [← inv_pow, ← hz]; exact h
      have h2 : omegaN N ^ (j : ℕ) = omegaN N ^ (k : ℕ) :=
        (inv_mul_eq_one₀ (pow_ne_zero _ hω0)).mp h'
      exact hjk (Fin.ext (hω.pow_inj j.isLt k.isLt h2))
    have hsum : ∑ l : Fin N, z ^ (l : ℕ) = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun l => z ^ l) N, geom_sum_eq hzne, hzN]
      simp
    rw [hsum]
    simp [hjk]

/-- **The 8-qubit QFT matrix is unitary.** -/
theorem qft_unitary_8 : qftQubits 8 ∈ Matrix.unitaryGroup (Fin (2 ^ 8)) ℂ := by
  have h : (qftQubits 8)ᴴ * qftQubits 8 = 1 :=
    qft_conjTranspose_mul_self (N := 2 ^ 8) (by norm_num)
  rw [Matrix.mem_unitaryGroup_iff']
  exact h

/-- The `8 × 8` (dimension-8) QFT matrix is unitary as well. -/
theorem qft_unitary_dim_8 : qft 8 ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  exact qft_conjTranspose_mul_self (N := 8) (by norm_num)

#print axioms QC.qft_unitary_8
#print axioms QC.qft_unitary_dim_8

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

