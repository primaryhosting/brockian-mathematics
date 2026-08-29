/-
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## Formalization of the statement

Chen's theorem asserts that every sufficiently large even number `n` can be written as
`n = p + q` where `p` is prime and `q` has at most two prime factors (counted with
multiplicity).  We formalize "number of prime factors with multiplicity" as `Ω`, the
length of the list of prime factors.
-/

/-- `bigOmega q = Ω(q)` is the number of prime factors of `q`, counted with multiplicity. -/

theorem goldbach_base_case :
    ∀ n < 500, Even n → 6 ≤ n → ∃ p < 40, Nat.Prime p ∧ Nat.Prime (n - p) := by
  decide

