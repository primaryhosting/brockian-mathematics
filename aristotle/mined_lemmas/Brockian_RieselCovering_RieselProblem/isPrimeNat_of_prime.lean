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


theorem isPrimeNat_of_prime {m : Nat} (hm : Nat.Prime m) : IsPrimeNat m :=
  ⟨hm.two_le, fun d hd => hm.eq_one_or_self_of_dvd d hd⟩

/-- For every `n ≥ 1`, `509203 * 2 ^ n - 1` is not prime (Mathlib's `Nat.Prime`). -/
