/-
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because a module docstring may not
-- precede the `import` command in Lean 4; the text is otherwise verbatim.)

import Mathlib

namespace Brockian

/-- The list of "wheel spokes": the primes below `100`, used as the small summand
in the binary (`K = 2`) Goldbach decompositions below. -/

def wheelSpokes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Finite verification: every even `n` with `4 ≤ n ≤ 947` can be written as `p + (n - p)`
with both `p` and `n - p` prime, where `p` is one of the wheel spokes (a prime below `100`). -/
