import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- The primitive `16`-th root of unity `exp (2πi/16)` used to build the 4-qubit QFT. -/

lemma qft_sum (j k : Fin 16) :
    ∑ n : Fin 16, qftZeta ^ (j.val * n.val) * (starRingEnd ℂ) (qftZeta ^ (k.val * n.val))
      = if j = k then (16 : ℂ) else 0 := by
  set d : ℤ := (j.val : ℤ) - (k.val : ℤ) with hd
  have hterm : ∀ n : Fin 16,
      qftZeta ^ (j.val * n.val) * (starRingEnd ℂ) (qftZeta ^ (k.val * n.val))
        = (qftZeta ^ d) ^ (n.val) := by
    intro n
    rw [conj_qftZeta_pow, ← zpow_natCast qftZeta (j.val * n.val),
      ← zpow_natCast qftZeta (k.val * n.val), ← zpow_neg, ← zpow_add₀ qftZeta_ne_zero,
      ← zpow_natCast (qftZeta ^ d) n.val, ← zpow_mul]
    congr 1
    push_cast [hd]
    ring
  rw [Finset.sum_congr rfl (fun n _ => hterm n)]
  by_cases hjk : j = k
  · subst hjk
    have : d = 0 := by simp [hd]
    simp [this]
  · have hd0 : d ≠ 0 := by
      simp only [hd, sub_ne_zero]
      exact_mod_cast fun h => hjk (Fin.ext (by exact_mod_cast h))
    have hdlt : d < 16 := by
      have : (j.val : ℤ) < 16 := by exact_mod_cast j.isLt
      omega
    have hdgt : -16 < d := by
      have : (k.val : ℤ) < 16 := by exact_mod_cast k.isLt
      omega
    have hnd : ¬ ((16 : ℤ) ∣ d) := by
      intro h
      obtain ⟨c, hc⟩ := h
      omega
    have hne1 : qftZeta ^ d ≠ 1 := by
      intro h
      exact hnd ((qftZeta_isPrimitiveRoot.zpow_eq_one_iff_dvd d).mp h)
    have hpow : (qftZeta ^ d) ^ (16 : ℕ) = 1 := by
      rw [← zpow_natCast (qftZeta ^ d) 16, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, qftZeta_pow_sixteen, one_zpow]
    rw [Fin.sum_univ_eq_sum_range (fun n => (qftZeta ^ d) ^ n) 16,
      geom_sum_eq hne1, hpow, sub_self, zero_div]
    simp [hjk]

/-- **The 4-qubit QFT matrix is unitary.** -/
