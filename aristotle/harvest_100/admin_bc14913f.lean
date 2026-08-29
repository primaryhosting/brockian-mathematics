/-
# Bertrand
Category: Frontier — Prime Numbers
Target: Primes.bertrand
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: the header above is written as a plain block comment `/- ... -/` rather than a
-- module docstring `/-! ... -/`, because Lean 4 does not allow any command (including a
-- module docstring) to appear before the `import` lines.

import Mathlib

/-!
# Bertrand
Category: Frontier — Prime Numbers
Target: Primes.bertrand
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Primes

/-- **Bertrand's postulate**: for every natural number `n` with `0 < n`, there exists a
prime `p` with `n < p ≤ 2 * n`. -/
theorem bertrand (n : ℕ) (hn : 0 < n) : ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 2 * n :=
  Nat.exists_prime_lt_and_le_two_mul n hn.ne'

end Primes

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

