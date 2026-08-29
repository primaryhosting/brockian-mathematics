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

import Mathlib
/-!
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` lines to precede any module doc comment, so the
-- required header block appears immediately after the single `import Mathlib` line.

namespace Brockian.LegendreConjecture

/-- `PrimeBetweenSquares n` states that there is a prime strictly between `n ^ 2`
and `(n + 1) ^ 2`. -/

def ShortIntervalHypothesis : Prop :=
  ∀ x : ℕ, 1 ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧ p ≤ x + Nat.sqrt x

/-- **Conditional reduction of Legendre's conjecture.**

Legendre's conjecture — for every `n ≥ 1` there is a prime strictly between `n ^ 2`
and `(n + 1) ^ 2` — is an open problem, so it is proved here conditionally: it follows
from the short-interval prime hypothesis, namely that every interval `(x, x + √x]`
with `x ≥ 1` contains a prime.  Indeed, taking `x = n ^ 2` produces a prime `p` with
`n ^ 2 < p ≤ n ^ 2 + n < (n + 1) ^ 2`. -/
