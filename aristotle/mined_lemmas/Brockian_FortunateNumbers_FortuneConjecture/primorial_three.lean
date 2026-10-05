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

theorem primorial_three : primorial 3 = 6 := by decide

/-- The Fortunate number of `0# = 1` is `2`, which is prime. -/
example : IsFortunate 0 2 := by
  refine ⟨by norm_num, by rw [primorial_zero]; norm_num, ?_⟩
  intro k hk1 hk2
  omega

/-- The Fortunate number of `2# = 2` is `3`, which is prime. -/
example : IsFortunate 2 3 := by
  refine ⟨by norm_num, by rw [primorial_two]; norm_num, ?_⟩
  intro k hk1 hk2
  rw [primorial_two]
  interval_cases k
  norm_num

/-- The Fortunate number of `3# = 6` is `5`, which is prime. -/
example : IsFortunate 3 5 := by
  refine ⟨by norm_num, by rw [primorial_three]; norm_num, ?_⟩
  intro k hk1 hk2
  rw [primorial_three]
  interval_cases k <;> norm_num

end Examples

end Brockian.FortunateNumbers

