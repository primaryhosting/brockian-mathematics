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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command, including module
-- doc comments, so the requested header comment appears verbatim immediately after the
-- single `import Mathlib` line.

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

theorem cullenPrimeConjecture_iff_forall_exists_ge :
    CullenPrimeConjecture ↔ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Nat.Prime (cullen n) := by
  constructor
  · intro h N
    obtain ⟨n, hn, hlt⟩ := h.exists_gt N
    exact ⟨n, hlt.le, hn⟩
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨n, hn, hp⟩ := h (a + 1)
    exact ⟨n, hp, by omega⟩

/-- The contrapositive form: the conjecture fails exactly when all sufficiently large
Cullen numbers are composite. -/
