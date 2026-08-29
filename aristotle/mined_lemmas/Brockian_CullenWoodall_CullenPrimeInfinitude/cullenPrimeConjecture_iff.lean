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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede every command, including module
-- docstrings, so the header above is a plain block comment and is repeated as a
-- module docstring after the import.)

import Mathlib

/-!
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

theorem cullenPrimeConjecture_iff :
    CullenPrimeConjecture ↔ ∀ N : ℕ, ∃ n, N < n ∧ (cullen n).Prime :=
  CullenPrimeInfinitude

/-- A sanity check: `C 1 = 3` is a Cullen prime, while `C 2 = 9` is not. -/
example : (cullen 1).Prime ∧ ¬ (cullen 2).Prime := by
  constructor
  · rw [cullen_one]; norm_num
  · unfold cullen; norm_num
    decide

end Brockian.CullenWoodall

