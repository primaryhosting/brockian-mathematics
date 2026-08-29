import Mathlib

/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset

/-- The primitive `2^n`-th root of unity used by the quantum Fourier transform. -/
noncomputable def qftRoot (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (2 ^ n))

/-- The matrix of the quantum Fourier transform on `n` qubits:
the `(j, k)` entry is `exp (2 π i j k / 2^n) / √(2^n)`. -/
noncomputable def qftMatrix (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun j k =>
    (1 / Real.sqrt (2 ^ n) : ℝ) *
      Complex.exp (2 * Real.pi * Complex.I * (j.val * k.val) / (2 ^ n))

lemma qftRoot_isPrimitiveRoot (n : ℕ) : IsPrimitiveRoot (qftRoot n) (2 ^ n) := by
  have h : ((2 : ℕ) ^ n : ℕ) ≠ 0 := by positivity
  have hcast : ((2 : ℂ) ^ n) = (((2 : ℕ) ^ n : ℕ) : ℂ) := by push_cast; ring
  rw [qftRoot, hcast]
  exact Complex.isPrimitiveRoot_exp _ h

lemma qftRoot_pow_card (n : ℕ) : (qftRoot n) ^ (2 ^ n) = 1 :=
  (qftRoot_isPrimitiveRoot n).pow_eq_one

lemma qftRoot_ne_zero (n : ℕ) : qftRoot n ≠ 0 := Complex.exp_ne_zero _

lemma conj_qftRoot (n : ℕ) : (starRingEnd ℂ) (qftRoot n) = (qftRoot n)⁻¹ := by
  rw [qftRoot, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, map_pow, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- The entries of the QFT matrix, written as powers of the root of unity. -/
lemma qftMatrix_apply (n : ℕ) (j k : Fin (2 ^ n)) :
    qftMatrix n j k = (1 / Real.sqrt (2 ^ n) : ℝ) * (qftRoot n) ^ (j.val * k.val) := by
  rw [qftMatrix, qftRoot, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- A geometric sum of a root of unity: it is `N` if the base is `1`, and `0` otherwise. -/
lemma sum_pow_of_pow_eq_one {N : ℕ} {z : ℂ} (hz : z ^ N = 1) :
    ∑ k ∈ Finset.range N, z ^ k = if z = 1 then (N : ℂ) else 0 := by
  by_cases h : z = 1
  · simp [h]
  · rw [if_neg h, geom_sum_eq h, hz, sub_self, zero_div]

/-- The key orthogonality relation for the rows of the QFT matrix. -/
lemma qft_orthogonality (n : ℕ) (j l : Fin (2 ^ n)) :
    ∑ k : Fin (2 ^ n), (qftRoot n) ^ (j.val * k.val) *
        (starRingEnd ℂ) ((qftRoot n) ^ (l.val * k.val))
      = if j = l then ((2 ^ n : ℕ) : ℂ) else 0 := by
  set w := qftRoot n with hw
  have hwne : w ≠ 0 := qftRoot_ne_zero n
  have hpow : w ^ (2 ^ n) = 1 := qftRoot_pow_card n
  set z : ℂ := w ^ j.val * (w ^ l.val)⁻¹ with hzdef
  have hjN : (w ^ j.val) ^ (2 ^ n) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow]
  have hlN : (w ^ l.val) ^ (2 ^ n) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow]
  have hzN : z ^ (2 ^ n) = 1 := by
    rw [hzdef, mul_pow, hjN, inv_pow, hlN]
    norm_num
  have hterm : ∀ k : Fin (2 ^ n),
      (w ^ (j.val * k.val)) * (starRingEnd ℂ) (w ^ (l.val * k.val)) = z ^ k.val := by
    intro k
    have hc : (starRingEnd ℂ) (w ^ (l.val * k.val)) = (w ^ (l.val * k.val))⁻¹ := by
      rw [map_pow, hw, conj_qftRoot, inv_pow]
    rw [hc, hzdef, mul_pow, inv_pow, ← pow_mul, ← pow_mul]
  have hiff : z = 1 ↔ j = l := by
    rw [hzdef, mul_inv_eq_one₀ (pow_ne_zero _ hwne)]
    constructor
    · intro h
      exact Fin.ext ((qftRoot_isPrimitiveRoot n).pow_inj j.isLt l.isLt h)
    · intro h; rw [h]
  calc ∑ k : Fin (2 ^ n), (w ^ (j.val * k.val)) * (starRingEnd ℂ) (w ^ (l.val * k.val))
      = ∑ k : Fin (2 ^ n), z ^ k.val := Finset.sum_congr rfl fun k _ => hterm k
    _ = ∑ k ∈ Finset.range (2 ^ n), z ^ k := Fin.sum_univ_eq_sum_range (fun k => z ^ k) _
    _ = if z = 1 then ((2 ^ n : ℕ) : ℂ) else 0 := sum_pow_of_pow_eq_one hzN
    _ = if j = l then ((2 ^ n : ℕ) : ℂ) else 0 := by
        by_cases h : j = l
        · rw [if_pos h, if_pos (hiff.mpr h)]
        · rw [if_neg h, if_neg (fun hz => h (hiff.mp hz))]

/-- The QFT matrix on `n` qubits is unitary. -/
theorem qft_unitary (n : ℕ) : qftMatrix n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hstar : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun _ => rfl
  have hsq : (Real.sqrt ((2 : ℝ) ^ n)) ^ 2 = (2 : ℝ) ^ n := Real.sq_sqrt (by positivity)
  have key : ∀ k : Fin (2 ^ n),
      qftMatrix n j k * (star (qftMatrix n) : Matrix _ _ ℂ) k l
        = ((1 / Real.sqrt (2 ^ n) : ℝ) : ℂ) ^ 2 *
          ((qftRoot n) ^ (j.val * k.val) * (starRingEnd ℂ) ((qftRoot n) ^ (l.val * k.val))) := by
    intro k
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, qftMatrix_apply,
      qftMatrix_apply, hstar, map_mul, Complex.conj_ofReal]
    ring
  rw [Finset.sum_congr rfl fun k _ => key k, ← Finset.mul_sum, qft_orthogonality]
  have hcoef : ((1 / Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) ^ 2 * ((2 ^ n : ℕ) : ℂ) = 1 := by
    have h1 : ((1 / Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) ^ 2 = ((1 / ((2 : ℝ) ^ n) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, div_pow, one_pow, hsq]
    rw [h1]
    push_cast
    field_simp
  by_cases h : j = l
  · rw [if_pos h, if_pos h]; exact hcoef
  · rw [if_neg h, if_neg h, mul_zero]

/-- The 7-qubit QFT matrix is unitary. -/
theorem qft_unitary_7 : qftMatrix 7 ∈ Matrix.unitaryGroup (Fin (2 ^ 7)) ℂ :=
  qft_unitary 7

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

