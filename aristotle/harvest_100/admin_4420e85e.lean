/-!
# Two Squares 61
Category: Pure Mathematics
Target: Math.two_squares_61
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires every `import` command to precede all other commands, including
-- module doc comments, so this file (which must begin with the header above) carries no
-- imports; the statement and its proof need nothing beyond Lean core.  A derivation of the
-- same statement from Mathlib's Fermat two-squares theorem `Nat.Prime.sq_add_sq` is given in
-- `RequestProject/TwoSquares61Fermat.lean`.

namespace Math

/-- The prime `61` is a sum of two squares: `61 = 5 ^ 2 + 6 ^ 2`. -/
theorem two_squares_61 : ∃ a b : Nat, a ^ 2 + b ^ 2 = 61 := ⟨5, 6, rfl⟩

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

import Mathlib
import RequestProject.TwoSquares61

/-!
# Two Squares 61, via Fermat's two-squares theorem

An alternative derivation of `Math.two_squares_61` from Mathlib's
`Nat.Prime.sq_add_sq`: every prime `p` with `p % 4 ≠ 3` is a sum of two squares.
-/

namespace Math

/-- `61` is a sum of two squares, obtained from Mathlib's general two-squares theorem
`Nat.Prime.sq_add_sq` rather than from explicit witnesses. -/
theorem two_squares_61_via_fermat : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 61 := by
  haveI : Fact (Nat.Prime 61) := ⟨by norm_num⟩
  exact Nat.Prime.sq_add_sq (p := 61) (by norm_num)

end Math

