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
import Brockian.SierpinskiCovering

/-!
# Sierpiński numbers: Mathlib-flavoured restatement

`Brockian/SierpinskiCovering.lean` must be import-free (its mandated header comment has to
precede everything, and Lean requires `import` to come first), so it develops the covering
argument using only the core `Nat` API.  Here we restate its conclusions with the usual
Mathlib vocabulary: `Nat.Prime`, `Odd`, and `Set.Infinite`.
-/

namespace Brockian.SierpinskiCovering

/-- A composite number is not prime. -/

theorem isSierpinskiNumber_78557 : IsSierpinskiNumber 78557 :=
  isSierpinskiNumber_of_mod (by decide) (by decide) rfl

/-- **Sierpiński's theorem (Sierpiński problem, covering-set solution).** There are
infinitely many Sierpiński numbers: for every bound `N` there is an odd `k > N` with
`k * 2 ^ n + 1` composite for all `n ≥ 1`. -/
