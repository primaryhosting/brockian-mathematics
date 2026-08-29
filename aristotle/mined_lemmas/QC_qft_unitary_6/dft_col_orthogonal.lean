import Mathlib

/-!
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

set_option grind.warning false

namespace QC

/-- The `N × N` discrete Fourier transform (QFT) matrix:
`F j k = exp (2 π i j k / N) / √N`. -/

lemma dft_col_orthogonal (N : ℕ) (hN : N ≠ 0) (j k : Fin N) :
    ∑ m : Fin N, (starRingEnd ℂ) (omegaN N ^ (m.val * j.val)) * omegaN N ^ (m.val * k.val)
      = if j = k then (N : ℂ) else 0 := by
  have hprim := Complex.isPrimitiveRoot_exp N hN
  set w : ℂ := omegaN N with hw
  have hwne : w ≠ 0 := omegaN_ne_zero N
  have hconj : (starRingEnd ℂ) w = w⁻¹ := by
    rw [hw, omegaN, ← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp only [map_div₀, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal, map_natCast]
    ring
  have hterm : ∀ m : Fin N,
      (starRingEnd ℂ) (w ^ (m.val * j.val)) * w ^ (m.val * k.val)
        = (w ^ ((k.val : ℤ) - (j.val : ℤ))) ^ (m.val : ℕ) := by
    intro m
    rw [map_pow, hconj, inv_pow, ← zpow_natCast w (m.val * j.val), ← zpow_natCast w (m.val * k.val),
      ← zpow_neg, ← zpow_natCast (w ^ ((k.val : ℤ) - (j.val : ℤ))) m.val, ← zpow_mul,
      ← zpow_add₀ hwne]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  set x : ℂ := w ^ ((k.val : ℤ) - (j.val : ℤ)) with hx
  rw [Fin.sum_univ_eq_sum_range (fun m => x ^ m) N]
  by_cases hjk : j = k
  · subst hjk
    have : x = 1 := by simp [hx]
    simp [this]
  · have hxne : x ≠ 1 := by
      rw [hx]
      intro h
      have hdvd : (N : ℤ) ∣ ((k.val : ℤ) - (j.val : ℤ)) := (hprim.zpow_eq_one_iff_dvd _).mp h
      have hd : N ∣ ((k.val : ℤ) - (j.val : ℤ)).natAbs := by
        simpa using Int.natAbs_dvd_natAbs.mpr hdvd
      have hne : j.val ≠ k.val := fun h2 => hjk (Fin.ext h2)
      have hj := j.isLt
      have hk := k.isLt
      have hpos : 0 < ((k.val : ℤ) - (j.val : ℤ)).natAbs := by omega
      have := Nat.le_of_dvd hpos hd
      omega
    have hxN : x ^ N = 1 := by
      rw [hx, ← zpow_natCast (w ^ _) N, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, omegaN_pow_N N hN, one_zpow]
    rw [geom_sum_eq hxne, hxN, sub_self, zero_div]
    simp [hjk]

