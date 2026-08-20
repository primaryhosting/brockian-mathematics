import Mathlib
import RequestProject.TwoSquares73

/-!
# Two Squares 73, via Mathlib's Fermat two-squares theorem

Companion file to `RequestProject/TwoSquares73.lean`: it derives the same statement
from Mathlib's `Nat.Prime.sq_add_sq`, and records that `73` is indeed prime.
-/

namespace Math

/-- `73` is prime. -/
theorem prime_73 : Nat.Prime 73 := by norm_num

/-- The prime `73` is a sum of two squares, obtained from Mathlib's Fermat
two-squares theorem `Nat.Prime.sq_add_sq` using `73 % 4 = 1`. -/
theorem two_squares_73_via_mathlib : ∃ a b : ℕ, (73 : ℕ) = a ^ 2 + b ^ 2 := by
  haveI : Fact (Nat.Prime 73) := ⟨prime_73⟩
  obtain ⟨a, b, h⟩ := Nat.Prime.sq_add_sq (p := 73) (by norm_num)
  exact ⟨a, b, h.symm⟩

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

/-!
# Two Squares 73
Category: Pure Mathematics
Target: Math.two_squares_73
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The prime `73` is a sum of two squares: `73 = 3 ^ 2 + 8 ^ 2`.

This is an instance of Fermat's two-squares theorem (Mathlib's `Nat.Prime.sq_add_sq`),
applicable since `73` is prime with `73 % 4 = 1`; see
`Math.two_squares_73_via_mathlib` in `RequestProject/TwoSquares73Mathlib.lean`
for the derivation from that lemma. Here we exhibit the explicit representation. -/
theorem two_squares_73 : ∃ a b : Nat, (73 : Nat) = a ^ 2 + b ^ 2 :=
  ⟨3, 8, rfl⟩

end Math

