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

/-
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-!`, so the header above
-- is reproduced verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- A *Sophie Germain prime* is a prime `p` such that `2 * p + 1` is also prime. -/

theorem sophieGermainSet_infinite_iff_unbounded :
    sophieGermainSet.Infinite ↔ ∀ N : ℕ, ∃ p : ℕ, N < p ∧ IsSophieGermain p := by
  rw [Set.infinite_iff_exists_gt]
  constructor
  · intro h N
    obtain ⟨p, hp, hlt⟩ := h N
    exact ⟨p, hlt, hp⟩
  · intro h N
    obtain ⟨p, hlt, hp⟩ := h N
    exact ⟨p, hp, hlt⟩

/-! ## The hypothesis: Dickson / Schinzel for two linear forms

`DicksonTwoForms` is the special case of Dickson's conjecture (equivalently, of Schinzel's
Hypothesis H for a product of two linear polynomials) asserting that an *admissible* pair of
linear forms `a * n + b`, `c * n + d` takes prime values simultaneously infinitely often.
Admissibility is the usual local condition: no prime divides the product `(a n + b)(c n + d)`
for every `n`. -/
