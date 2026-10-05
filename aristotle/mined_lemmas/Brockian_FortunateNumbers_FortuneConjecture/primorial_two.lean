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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Note: the requested header is written as a plain block comment `/- ... -/` rather than a
-- module doc comment `/-! ... -/`, because Lean 4 requires `import` to precede every command,
-- and a module doc comment counts as a command.  The text is otherwise verbatim.)

import Mathlib

set_option maxHeartbeats 1000000

namespace Brockian.FortunateNumbers

open Finset

/-- `IsFortunate n m` says that `m` is *the* Fortunate number attached to the primorial `n#`:
it is the least integer `m > 1` such that `n# + m` is prime. -/

theorem primorial_two : primorial 2 = 2 := by decide

