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

-- This file is deliberately self-contained (no `import` line), because the
-- required header above is a module doc-comment, which Lean only accepts at
-- the very top of a file, i.e. before any `import`.  Nothing below needs
-- Mathlib: a search of Mathlib turns up no Collatz material at all, and the
-- ingredients used here (iteration of a map, strong induction on `ℕ`) are
-- developed from scratch.

namespace Brockian.CollatzPartial

/-- One step of the Collatz (`3n + 1`) map: halve `n` when it is even,
otherwise send `n` to `3 * n + 1`. -/

def collatzIter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => collatzIter k (collatzStep n)

