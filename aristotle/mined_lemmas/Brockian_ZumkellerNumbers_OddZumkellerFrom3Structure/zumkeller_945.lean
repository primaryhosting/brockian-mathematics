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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Brockian
namespace ZumkellerNumbers

/-- A positive natural number `n` is a *Zumkeller number* if the set of its divisors can be
split into two parts having the same sum. -/

theorem zumkeller_945 : Zumkeller 945 :=
  ⟨by norm_num, {15, 945}, by decide, by decide⟩

/-- **Odd Zumkeller numbers from the `3`-structure `945 = 3 ^ 3 · 5 · 7`.**
For every odd `m` coprime to `945`, the number `945 * m` is an odd Zumkeller number,
and it is divisible by `27`. -/
