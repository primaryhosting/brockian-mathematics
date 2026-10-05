/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/

lemma mem_exceptionalSet_one_eight_nine : ((1, 8, 9) : ℕ × ℕ × ℕ) ∈ exceptionalSet 0 := by
  have h72 : (1 * 8 * 9 : ℕ) = 72 := by norm_num
  have hrad : rad (1 * 8 * 9) = 6 := by
    rw [h72]
    simp [rad, Nat.primeFactors, show (72 : ℕ) = 2 ^ 3 * 3 ^ 2 by norm_num]
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by decide⟩, ?_⟩
  show ((rad (1 * 8 * 9) : ℝ)) ^ (1 + (0 : ℝ)) < ((9 : ℕ) : ℝ)
  rw [hrad]
  norm_num

/-- **The abc conjecture, reduced**: the finiteness formulation of the abc conjecture is
equivalent to the effective-shape formulation with an implied constant. -/
