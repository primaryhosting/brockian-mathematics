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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.CarmichaelKorselt

/-- Korselt's criterion, used here as the definition of a Carmichael number:
`n` is composite (`1 < n` and not prime), squarefree, and `p - 1 ∣ n - 1`
for every prime `p` dividing `n`. -/

theorem isThreePrimeCarmichael_1729 : IsThreePrimeCarmichael 1729 := by
  have h := isThreePrimeCarmichael_chernick (k := 1) le_rfl (by norm_num) (by norm_num)
    (by norm_num)
  norm_num at h
  exact h

/-- **Conditional infinitude of three-prime Carmichael numbers.**

The unconditional infinitude of Carmichael numbers with exactly three prime factors is an
open problem, so this is a Lean-checked *conditional reduction*: it derives the infinitude
from the (conjectural, a special case of Dickson's conjecture) hypothesis that the linear
forms `6k+1, 12k+1, 18k+1` are simultaneously prime infinitely often.  The construction is
Chernick's, and the Carmichael property is verified through Korselt's criterion. -/
