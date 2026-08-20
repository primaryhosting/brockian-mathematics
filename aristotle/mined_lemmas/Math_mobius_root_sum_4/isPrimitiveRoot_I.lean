import Mathlib

/-!
# Mobius Root Sum 4
Category: Pure Mathematics
Target: Math.mobius_root_sum_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open Finset Complex

namespace Math

/-- `Complex.I` is a primitive 4-th root of unity. -/

theorem isPrimitiveRoot_I : IsPrimitiveRoot Complex.I 4 := by
  rw [IsPrimitiveRoot.iff_def]
  refine ⟨by norm_num, ?_⟩
  intro l hl
  have hpow : Complex.I ^ (l % 4) = 1 := by
    conv_rhs => rw [← hl]
    rw [← Nat.div_add_mod l 4, pow_add, pow_mul]
    norm_num
  have hcases : l % 4 = 0 ∨ l % 4 = 1 ∨ l % 4 = 2 ∨ l % 4 = 3 := by omega
  rcases hcases with h | h | h | h
  · exact Nat.dvd_of_mod_eq_zero h
  all_goals
    exfalso
    rw [h] at hpow
    norm_num [pow_succ, Complex.I_mul_I, Complex.ext_iff] at hpow

/-- The primitive 4-th roots of unity in `ℂ` are exactly `I` and `-I`. -/
