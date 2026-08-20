import Mathlib

/-!
# Two Squares 5 (Mathlib derivation)

Companion to `RequestProject/TwoSquares5.lean`: here we record that `5` is prime and
that it is a sum of two squares, obtained from Mathlib's Fermat two-squares theorem
`Nat.Prime.sq_add_sq`.
-/

namespace Math

/-- `5` is prime and is a sum of two squares, via `Nat.Prime.sq_add_sq`
(Fermat's two-squares theorem, applicable since `5 % 4 ≠ 3`). -/
theorem two_squares_5_prime : Nat.Prime 5 ∧ ∃ a b : ℕ, a ^ 2 + b ^ 2 = 5 :=
  ⟨by norm_num, by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact Nat.Prime.sq_add_sq (p := 5) (by norm_num)⟩

end Math

/-!
# Two Squares 5
Category: Pure Mathematics
Target: Math.two_squares_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header above is a module docstring, which must be the first
-- command in the file; Lean therefore forbids any `import` after it. This file is
-- consequently import-free (the proof needs nothing beyond core Lean). The
-- Mathlib-based derivation, via the Fermat two-squares theorem
-- `Nat.Prime.sq_add_sq`, is in `RequestProject/TwoSquares5Mathlib.lean`.

namespace Math

/-- The prime `5` is a sum of two squares: `5 = 1 ^ 2 + 2 ^ 2`. -/
theorem two_squares_5 : ∃ a b : Nat, 5 = a ^ 2 + b ^ 2 :=
  ⟨1, 2, by decide⟩

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

