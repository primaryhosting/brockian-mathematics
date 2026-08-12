/-
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace QC

/-- The (normalized) discrete Fourier transform matrix of size `N` built from a
complex number `z`: its `(j, k)` entry is `z ^ (j * k) / √N`. -/
noncomputable def dftMatrix (N : ℕ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => z ^ (j.val * k.val) / Real.sqrt N

/-- The quantum Fourier transform matrix on `n` qubits, i.e. the `2 ^ n`-dimensional
DFT matrix with `z = exp (2 π i / 2 ^ n)`:
`(QFT_n)_{j,k} = exp (2 π i j k / 2 ^ n) / √(2 ^ n)`. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  dftMatrix (2 ^ n) (Complex.exp (2 * Real.pi * Complex.I / (2 ^ n : ℕ)))

/-- If `z` is a primitive `N`-th root of unity, the normalized DFT matrix of size `N`
is unitary. -/
theorem dftMatrix_mem_unitaryGroup (N : ℕ) [NeZero N] (z : ℂ) (hprim : IsPrimitiveRoot z N) :
    dftMatrix N z ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hzN : z ^ N = 1 := hprim.pow_eq_one
  have hnorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hzN (NeZero.ne N)
  have hmul : z * z ^ (N - 1) = 1 := by
    rw [← pow_succ']
    have h : N - 1 + 1 = N := by omega
    rw [h, hzN]
  have hconj : (starRingEnd ℂ) z = z ^ (N - 1) := by
    rw [← Complex.inv_eq_conj hnorm]
    exact inv_eq_of_mul_eq_one_right hmul
  have hsq : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    norm_num
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [Matrix.mem_unitaryGroup_iff]
  ext j k
  rw [Matrix.mul_apply]
  -- Each summand is `(z ^ (j + (N-1) k)) ^ m / N`.
  have key : ∀ m : Fin N, dftMatrix N z j m * (star (dftMatrix N z)) m k
      = (z ^ (j.val + (N - 1) * k.val)) ^ m.val / (N : ℂ) := by
    intro m
    rw [Matrix.star_apply]
    simp only [dftMatrix, RCLike.star_def, map_div₀, map_pow, hconj, Complex.conj_ofReal]
    rw [div_mul_div_comm, hsq, ← pow_mul, ← pow_mul, ← pow_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun m _ => key m), ← Finset.sum_div]
  -- `N ∣ j + (N-1) k` exactly when `j = k`.
  have hdvd : N ∣ (j.val + (N - 1) * k.val) ↔ j = k := by
    constructor
    · intro h
      have h0 : ((j.val + (N - 1) * k.val : ℕ) : ZMod N) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 h
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hN] at h0
      simp at h0
      have hjk : ((j.val : ℕ) : ZMod N) = ((k.val : ℕ) : ZMod N) := by linear_combination h0
      have hv := congrArg ZMod.val hjk
      rw [ZMod.val_cast_of_lt j.isLt, ZMod.val_cast_of_lt k.isLt] at hv
      exact Fin.ext hv
    · rintro rfl
      refine ⟨j.val, ?_⟩
      cases N with
      | zero => omega
      | succ n => simp; ring
  by_cases hjk : j = k
  · have h1 : z ^ (j.val + (N - 1) * k.val) = 1 := (hprim.pow_eq_one_iff_dvd _).2 (hdvd.2 hjk)
    rw [h1, show (1 : Matrix (Fin N) (Fin N) ℂ) j k = 1 from by
      rw [hjk]; exact Matrix.one_apply_eq k]
    simp [Finset.card_univ]
  · have h1 : z ^ (j.val + (N - 1) * k.val) ≠ 1 := fun h =>
      hjk (hdvd.1 ((hprim.pow_eq_one_iff_dvd _).1 h))
    have hpow : (z ^ (j.val + (N - 1) * k.val)) ^ N = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hzN, one_pow]
    rw [Fin.sum_univ_eq_sum_range (fun m => (z ^ (j.val + (N - 1) * k.val)) ^ m) N,
      geom_sum_eq h1, hpow, Matrix.one_apply_ne hjk]
    simp

/-- The `n`-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_mem_unitaryGroup (n : ℕ) :
    qft n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  exact dftMatrix_mem_unitaryGroup (2 ^ n) _
    (Complex.isPrimitiveRoot_exp (2 ^ n) (by positivity))

/-- **The 3-qubit QFT matrix is unitary.** -/
theorem qft_unitary_3 : qft 3 ∈ Matrix.unitaryGroup (Fin (2 ^ 3)) ℂ :=
  qft_mem_unitaryGroup 3

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

