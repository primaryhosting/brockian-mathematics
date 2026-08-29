import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/

lemma abc_exceptions_zero_infinite : (AbcExceptions 0).Infinite :=
  Set.infinite_of_injective_forall_mem wit_injective wit_mem

/-! ### Reduction to small `ε` -/

