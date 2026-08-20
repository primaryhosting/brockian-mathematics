/-
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex

namespace QC

/-- The primitive `2^7 = 128`-th root of unity `exp (2πi/128)`. -/

lemma qft_sum (a b : Fin 128) :
    ∑ k : Fin 128, (starRingEnd ℂ) (qftOmega ^ (k.val * a.val)) * qftOmega ^ (k.val * b.val)
      = if a = b then (128 : ℂ) else 0 := by
  set x : ℂ := (starRingEnd ℂ) (qftOmega ^ a.val) * qftOmega ^ b.val with hx
  have hterm : ∀ k : Fin 128,
      (starRingEnd ℂ) (qftOmega ^ (k.val * a.val)) * qftOmega ^ (k.val * b.val) = x ^ k.val := by
    intro k
    rw [hx, mul_pow, mul_comm k.val a.val, mul_comm k.val b.val, pow_mul, pow_mul, map_pow]
  have hxn : x ^ (128 : ℕ) = 1 := by
    rw [hx, mul_pow, ← map_pow, ← pow_mul, ← pow_mul, mul_comm a.val 128, mul_comm b.val 128,
      pow_mul, pow_mul, qftOmega_pow, one_pow, one_pow, map_one, mul_one]
  have hconj : (starRingEnd ℂ) (qftOmega ^ a.val) = (qftOmega ^ a.val)⁻¹ := by
    rw [map_pow, conj_qftOmega, inv_pow]
  have hx1 : x = 1 ↔ a = b := by
    constructor
    · intro h
      rw [hx, hconj] at h
      have hne : qftOmega ^ a.val ≠ 0 := pow_ne_zero _ qftOmega_ne_zero
      have h2 : qftOmega ^ b.val = qftOmega ^ a.val := by
        field_simp at h
        linear_combination h
      exact Fin.ext (qftOmega_prim.pow_inj a.isLt b.isLt h2.symm)
    · rintro rfl
      rw [hx, hconj, inv_mul_cancel₀ (pow_ne_zero _ qftOmega_ne_zero)]
  rw [Finset.sum_congr rfl fun k _ => hterm k]
  have hrange : ∑ k : Fin 128, x ^ k.val = ∑ k ∈ Finset.range 128, x ^ k :=
    (Finset.sum_range fun i => x ^ i).symm
  rw [hrange]
  by_cases h : a = b
  · rw [if_pos h, hx1.mpr h]
    simp
  · rw [if_neg h, geom_sum_eq (fun hc => h (hx1.mp hc)), hxn, sub_self, zero_div]

