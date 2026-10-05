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
