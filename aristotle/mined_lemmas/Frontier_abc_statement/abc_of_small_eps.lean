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

theorem abc_of_small_eps (h : ∀ ε : ℝ, 0 < ε → ε < 1 → (exceptionalSet ε).Finite) :
    ABCConjecture := by
  intro ε hε
  rcases lt_or_ge ε 1 with hlt | hge
  · exact h ε hε hlt
  · exact Set.Finite.subset (h (1 / 2) (by norm_num) (by norm_num))
      (exceptionalSet_subset_of_le (by linarith))

/-- A concrete exceptional triple: `1 + 8 = 9` with `rad (1 * 8 * 9) = 6 < 9`. -/
