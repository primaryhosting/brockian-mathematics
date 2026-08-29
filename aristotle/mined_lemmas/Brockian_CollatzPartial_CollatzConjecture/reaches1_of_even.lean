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

theorem reaches1_of_even {n : Nat} (he : n % 2 = 0) (h : Reaches1 (n / 2)) : Reaches1 n := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k + 1, ?_⟩
  rw [collatzIter_succ']
  unfold collatz
  rw [if_pos he]
  exact hk

/-- If `n` is odd and `3 * n + 1` reaches `1`, then so does `n`. -/
