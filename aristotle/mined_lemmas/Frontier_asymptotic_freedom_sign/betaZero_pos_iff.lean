/-
# Asymptotic Freedom Sign
Category: Frontier Physics
Target: Frontier.asymptotic_freedom_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Asymptotic Freedom Sign
Category: Frontier Physics
Target: Frontier.asymptotic_freedom_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Real

/-- The one-loop beta-function coefficient `b₀` for an `SU(N)` gauge theory with
`Nf` Dirac fermions in the fundamental representation:
`b₀ = 11 N / 3 - 2 Nf / 3`. -/

theorem betaZero_pos_iff (N Nf : ℕ) : 0 < betaZero N Nf ↔ 2 * Nf < 11 * N := by
  rw [betaZero, sub_pos, div_lt_div_iff_of_pos_right (by norm_num : (0:ℝ) < 3)]
  constructor
  · intro h
    have : (2 * Nf : ℝ) < 11 * N := by push_cast at h ⊢; linarith
    exact_mod_cast this
  · intro h
    have : (2 * Nf : ℝ) < (11 * N : ℝ) := by exact_mod_cast h
    push_cast at this ⊢
    linarith

/-- **Asymptotic freedom sign.** For an `SU(N)` gauge theory with `Nf` fundamental Dirac
fermions satisfying `2 Nf < 11 N` (in particular the pure-gauge case `Nf = 0` with `N ≥ 1`),
the one-loop beta function is strictly negative at every positive coupling `g`: the coupling
decreases with increasing energy scale. -/
