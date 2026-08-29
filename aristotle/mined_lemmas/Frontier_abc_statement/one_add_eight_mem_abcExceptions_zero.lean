/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The radical of `n`: the product of the distinct prime factors of `n`. -/

theorem one_add_eight_mem_abcExceptions_zero : ((1 : ℕ), (8 : ℕ), (9 : ℕ)) ∈ abcExceptions 0 := by
  refine ⟨by norm_num, by norm_num, by decide, by norm_num, ?_⟩
  have : rad (1 * 8 * 9) = 6 := rad_eight_nine
  rw [this]
  norm_num

end Frontier

