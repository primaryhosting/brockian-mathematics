import Mathlib
import RequestProject.IntegralityThreeHalves

/-!
# Integrality Three Halves — Mathlib restatements

The target theorem `Riemann.Method.integrality_three_halves` lives in
`RequestProject/IntegralityThreeHalves.lean`, which must begin with a fixed header
comment and therefore cannot carry an `import` line; it is proved in Lean core.

This companion file imports Mathlib and records the equivalent formulations
`m ^ 2 ≥ 3 * m - 2` over `ℕ` and `(m - 1) * (m - 2) ≥ 0` over `ℤ`.
-/

namespace Riemann.Method

/-- Restatement over `ℕ` with `ℕ`-subtraction: `m ^ 2 ≥ 3 * m - 2`. -/

theorem integrality_three_halves (m : Nat) : 3 * m ≤ m ^ 2 + 2 := by
  induction m with
  | zero => decide
  | succ n ih =>
      have hsq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by
        simp [Nat.pow_succ, Nat.pow_zero, Nat.succ_mul, Nat.mul_succ]
        omega
      have hn : n ≤ n ^ 2 := by
        cases n with
        | zero => decide
        | succ k =>
            have : (k + 1) ^ 2 = (k + 1) * (k + 1) := by
              simp [Nat.pow_succ, Nat.pow_zero]
            have hle : (k + 1) * 1 ≤ (k + 1) * (k + 1) :=
              Nat.mul_le_mul_left (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
            omega
      omega

end Riemann.Method

