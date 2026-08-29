/-
# Landau Levels — a concrete model
A Fock-space realization of the ladder-operator hypotheses used in
`Frontier.landau_levels`, showing that they are consistent and that every
level `ℏ ω_c (n + 1/2)` really occurs.
-/

import Mathlib
import RequestProject.LandauLevels

namespace Frontier.Fock

/-! ### The inner product on finitely supported sequences -/

/-- The Fock inner product on finitely supported complex sequences. -/

theorem fock_ccr (x : ℕ →₀ ℂ) : aOp (adagOp x) - adagOp (aOp x) = x := by
  ext k
  have hk1 : (Real.sqrt ((k : ℝ) + 1) : ℂ) * (Real.sqrt ((k : ℝ) + 1) : ℂ) = ((k : ℂ) + 1) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  by_cases h0 : k = 0
  · subst h0
    simp only [Finsupp.sub_apply, aOp_apply, adagOp_apply, if_true, sub_zero]
    norm_num
  · have hk0 : (Real.sqrt (k : ℝ) : ℂ) * (Real.sqrt (k : ℝ) : ℂ) = (k : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      norm_num
    have hsucc : k - 1 + 1 = k := by omega
    have hcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
      have h1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [h1]; ring
    simp only [Finsupp.sub_apply, aOp_apply, adagOp_apply, h0, if_false, hsucc,
      Nat.add_sub_cancel]
    push_cast
    rw [← mul_assoc, hk1, hcast, ← mul_assoc, hk0]
    ring

