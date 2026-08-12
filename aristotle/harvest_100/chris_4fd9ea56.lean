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
theorem integrality_three_halves_sub (m : ℕ) : 3 * m - 2 ≤ m ^ 2 :=
  Nat.sub_le_of_le_add (integrality_three_halves m)

/-- Restatement over `ℤ`: `(m - 1) * (m - 2) ≥ 0` for a natural number `m`. -/
theorem integrality_three_halves_int (m : ℕ) : 0 ≤ ((m : ℤ) - 1) * ((m : ℤ) - 2) := by
  have h : (3 * m : ℤ) ≤ (m : ℤ) ^ 2 + 2 := by
    exact_mod_cast (by exact_mod_cast integrality_three_halves m : (3 * m : ℕ) ≤ (m ^ 2 + 2 : ℕ))
  nlinarith [h]

end Riemann.Method

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

/-!
# Integrality Three Halves
Category: Riemann Program
Target: Riemann.Method.integrality_three_halves
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Method

/-- For every natural number `m`, `3 * m ≤ m ^ 2 + 2`; equivalently `(m - 1) * (m - 2) ≥ 0`. -/
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

