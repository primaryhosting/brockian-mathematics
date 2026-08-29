import Mathlib

/-!
# Two Squares 37 — via Mathlib's Fermat two-squares theorem

Companion to `RequestProject/Math.lean`.  The main target `Math.two_squares_37`
is stated and proved there without any imports (so that the required header
comment can begin the file); here we record the same existence statement as a
consequence of Mathlib's `Nat.Prime.sq_add_sq`.
-/

namespace Math

/-- `37` is a sum of two squares, derived from Fermat's two-squares theorem
(`Nat.Prime.sq_add_sq`) applied to the prime `37 ≡ 1 [MOD 4]`. -/
theorem two_squares_37_mathlib : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  exact Nat.Prime.sq_add_sq (p := 37) (by norm_num)

end Math

/-!
# Two Squares 37
Category: Pure Mathematics
Target: Math.two_squares_37
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Every divisor of `37` below `38` is `1` or `37` (a finite check). -/
theorem divisors_37_lt : ∀ m < 38, m ∣ 37 → m = 1 ∨ m = 37 := by decide

/-- `37` is prime: it is at least `2` and its only divisors are `1` and `37`. -/
theorem prime_37 : 2 ≤ 37 ∧ ∀ m : Nat, m ∣ 37 → m = 1 ∨ m = 37 :=
  ⟨by decide, fun m hm =>
    divisors_37_lt m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm⟩

/-- **The prime 37 is a sum of two squares**: `37 = 1 ^ 2 + 6 ^ 2`.

The existence of such a representation for `37` is also an instance of Fermat's
two-squares theorem, available in Mathlib as `Nat.Prime.sq_add_sq` (applicable
since `37 % 4 = 1`); see `Math.two_squares_37_mathlib` in
`RequestProject/TwoSquaresMathlib.lean` for that derivation. -/
theorem two_squares_37 :
    (2 ≤ 37 ∧ ∀ m : Nat, m ∣ 37 → m = 1 ∨ m = 37) ∧ ∃ a b : Nat, a ^ 2 + b ^ 2 = 37 :=
  ⟨prime_37, 1, 6, rfl⟩

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

