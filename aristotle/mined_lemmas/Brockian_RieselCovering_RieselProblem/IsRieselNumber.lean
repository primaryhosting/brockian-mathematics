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
import Brockian.RieselCovering

/-!
# Riesel problem, Mathlib-facing statement

`Brockian.RieselCovering` must begin with a mandated header comment, which forces it to be
import-free (Lean requires `import`s to come first in a file).  This module imports Mathlib and
restates the main result using Mathlib's `Nat.Prime`.
-/

namespace Brockian
namespace RieselCovering


def IsRieselNumber (k : Nat) : Prop :=
  k % 2 = 1 ∧ 0 < k ∧ ∀ n : Nat, 1 ≤ n → ¬ IsPrimeNat (k * 2 ^ n - 1)

/-- Covering-set step.  If `p` divides `2 ^ 24 - 1 = 16777215` (so `2` has order dividing `24`
modulo `p`) and `p` divides `509203 * 2 ^ r - 1`, then `p` divides `509203 * 2 ^ n - 1` for
every `n ≡ r [MOD 24]`. -/
