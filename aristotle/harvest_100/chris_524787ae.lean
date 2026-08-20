import Mathlib
import RequestProject.TwoSquares97

/-!
# Two Squares 97, via Fermat's two-squares theorem

A Mathlib-based derivation of `Math.two_squares_97`, using
`Nat.Prime.sq_add_sq`.
-/

namespace Math

/-- `97` is a sum of two squares, derived from Mathlib's Fermat two-squares
theorem `Nat.Prime.sq_add_sq`. -/
theorem two_squares_97_via_fermat : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 97 :=
  haveI : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  Nat.Prime.sq_add_sq (p := 97) (by norm_num)

end Math

/-!
# Two Squares 97
Category: Pure Mathematics
Target: Math.two_squares_97
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The prime `97` is a sum of two squares: `97 = 9 ^ 2 + 4 ^ 2`.

This file is deliberately import-free so that the required header comment can be
the very first thing in the file (Lean requires `import` lines to precede all
other commands, including module docstrings).  A derivation of the same
statement from Mathlib's Fermat two-squares theorem `Nat.Prime.sq_add_sq`
(`p.Prime → p % 4 ≠ 3 → ∃ a b, a ^ 2 + b ^ 2 = p`, applicable since `97 % 4 = 1`)
is given in `RequestProject.TwoSquares97Fermat`. -/
theorem two_squares_97 : ∃ a b : Nat, a ^ 2 + b ^ 2 = 97 := ⟨9, 4, rfl⟩

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

