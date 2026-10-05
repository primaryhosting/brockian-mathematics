import Mathlib

/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires all `import` commands to come before any other command,
-- including module docstrings, so `import Mathlib` precedes the header above.

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000

namespace Brockian

/-- A kernel-friendly primality certificate: `n` has no divisor `d` with
`2 ≤ d ≤ 52` and `d * d ≤ n`.  For `n < 53 ^ 2 = 2809` this is equivalent to
primality of `n` (given `2 ≤ n`). -/

theorem goldbachWitnesses_keys :
    goldbachWitnesses.map Prod.fst = List.range' 4 1326 2 := by
  decide

