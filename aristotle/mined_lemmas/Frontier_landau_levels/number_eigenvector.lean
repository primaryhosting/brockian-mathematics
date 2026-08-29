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

theorem number_eigenvector (n : ℕ) :
    adagOp (aOp (Finsupp.single n (1 : ℂ))) = (n : ℂ) • Finsupp.single n (1 : ℂ) := by
  rw [aOp_single, adagOp_single, Finsupp.smul_single, smul_eq_mul, mul_one, mul_one]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have hsucc : n - 1 + 1 = n := by omega
    rw [hsucc]
    congr 1
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub hn]
        norm_num
      rw [this]; ring
    rw [hcast, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    norm_num

