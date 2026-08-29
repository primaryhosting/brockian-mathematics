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

/-!
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean forbids `import` commands after a module docstring. So, in order for the
-- required header above to be the very first thing in the file, this development is
-- written to be self-contained: it uses only the Lean core prelude, with no `import`.

namespace Brockian.CollatzPartial

/-- The Collatz step: `n ↦ n / 2` for even `n`, and `n ↦ 3 * n + 1` for odd `n`. -/

def reach1B : Nat → Nat → Bool
  | 0, n => n == 1
  | fuel + 1, n => n == 1 || reach1B fuel (collatz n)

/-- The bounded search is sound: a successful search witnesses `Reaches1`. -/
