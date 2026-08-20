/-!
# Two Squares 89
Category: Pure Mathematics
Target: Math.two_squares_89
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 89.**  The number `89` is prime (every natural divisor of it is
`1` or `89`) and it is a sum of two squares, namely `89 = 5 ^ 2 + 8 ^ 2`.

The header comment required for this file must be the very first thing in the file, and
Lean 4 forbids `import` commands after a module doc comment, so this file is written in
core Lean without importing Mathlib.  A Mathlib-based proof, deriving the decomposition
from `Nat.Prime.sq_add_sq` (Fermat's two-squares theorem, as `p % 4 ≠ 3`), is given in
`RequestProject/TwoSquares89Mathlib.lean`. -/
theorem two_squares_89 :
    (∀ m : Nat, m ∣ 89 → m = 1 ∨ m = 89) ∧ ∃ a b : Nat, (89 : Nat) = a ^ 2 + b ^ 2 := by
  refine ⟨?_, 5, 8, rfl⟩
  have hb : ∀ m : Nat, m < 90 → m ∣ 89 → m = 1 ∨ m = 89 := by decide
  intro m hm
  exact hb m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

end Math

import Mathlib

/-!
# Two Squares 89 (Mathlib version)

A Mathlib-based companion to `RequestProject/TwoSquares89.lean`: the prime `89` is a sum
of two squares, obtained from Fermat's two-squares theorem `Nat.Prime.sq_add_sq`.
-/

namespace Math

/-- `89` is prime and is a sum of two squares, via `Nat.Prime.sq_add_sq`. -/
theorem two_squares_89_mathlib :
    Nat.Prime 89 ∧ ∃ a b : ℕ, a ^ 2 + b ^ 2 = 89 := by
  have hp : Nat.Prime 89 := by norm_num
  haveI : Fact (Nat.Prime 89) := ⟨hp⟩
  exact ⟨hp, Nat.Prime.sq_add_sq (by norm_num)⟩

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

