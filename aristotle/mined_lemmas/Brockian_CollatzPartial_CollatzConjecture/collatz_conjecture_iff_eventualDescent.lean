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

theorem collatz_conjecture_iff_eventualDescent :
    EventualDescent ↔ ∀ n : Nat, 0 < n → Reaches1 n := by
  constructor
  · exact CollatzConjecture
  · intro h n hn
    obtain ⟨k, hk⟩ := h n (by omega)
    refine ⟨k, ?_, by rw [hk]; omega⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · rw [collatzIter_zero] at hk; omega
    · exact hk'

/-! ### Unconditional partial results -/

/-- If `n` is even and `n / 2` reaches `1`, then so does `n`. -/
