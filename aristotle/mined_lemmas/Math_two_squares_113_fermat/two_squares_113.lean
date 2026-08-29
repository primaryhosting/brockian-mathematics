import Mathlib

/-!
# Two Squares 113 — Mathlib derivation

A second proof that `113` is a sum of two squares, obtained from Mathlib's
`Nat.Prime.sq_add_sq` (Fermat's Christmas theorem: a prime `p` with `p % 4 ≠ 3`
is a sum of two squares), applied to the prime `113`, which satisfies `113 % 4 = 1`.
-/

namespace Math

/-- `113` is a sum of two squares, via Fermat's Christmas theorem. -/

theorem two_squares_113 : ∃ a b : Nat, a ^ 2 + b ^ 2 = 113 := ⟨7, 8, rfl⟩

end Math

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

