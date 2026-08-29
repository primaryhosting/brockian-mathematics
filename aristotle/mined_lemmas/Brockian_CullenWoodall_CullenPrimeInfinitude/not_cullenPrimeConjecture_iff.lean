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

theorem not_cullenPrimeConjecture_iff :
    ¬ CullenPrimeConjecture ↔ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ Nat.Prime (cullen n) := by
  rw [cullenPrimeConjecture_iff_forall_exists_ge]
  push_neg
  rfl

/-! ## A sieve criterion -/

/-- Trial-division criterion: a number `≥ 2` with no prime factor `p` satisfying `p * p ≤ m`
is prime. -/
