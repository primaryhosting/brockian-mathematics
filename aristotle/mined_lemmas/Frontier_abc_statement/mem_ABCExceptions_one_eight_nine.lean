import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the single `import Mathlib` line, since Lean 4
requires `import` commands to precede all other commands, including module docstrings.)
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

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/

lemma mem_ABCExceptions_one_eight_nine :
    ((1, 8, 9) : ℕ × ℕ × ℕ) ∈ ABCExceptions (1 / 5) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have hrad : rad (1 * 8 * 9) = 6 := by norm_num [rad_72]
  rw [hrad]
  have h65 : (1 : ℝ) + 1 / 5 = (6 : ℝ) / 5 := by norm_num
  rw [h65]
  have h5 : ((6 : ℝ) ^ ((6 : ℝ) / 5)) ^ (5 : ℕ) = 6 ^ (6 : ℕ) := by
    rw [← Real.rpow_natCast ((6 : ℝ) ^ ((6 : ℝ) / 5)) 5, ← Real.rpow_mul (by norm_num)]
    norm_num
  by_contra hcon
  push_neg at hcon
  have h : ((9 : ℕ) : ℝ) ^ (5 : ℕ) ≤ ((6 : ℝ) ^ ((6 : ℝ) / 5)) ^ (5 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) hcon 5
  rw [h5] at h
  norm_num at h

/-- For every `ε ≤ 1/5` there is at least one `abc`-exception. -/
