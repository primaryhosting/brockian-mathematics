import Mathlib
import RequestProject.TwoSquares13

/-!
# Two Squares 13 (Mathlib phrasing)

A companion to `RequestProject/TwoSquares13.lean`, restating the result with
Mathlib's `Nat.Prime`.
-/

namespace Math

/-- The prime `13` is a sum of two squares: `13 = 2 ^ 2 + 3 ^ 2`. -/
theorem two_squares_13_prime : Nat.Prime 13 ∧ ∃ a b : ℕ, 13 = a ^ 2 + b ^ 2 :=
  ⟨(Nat.prime_def_lt.2 ⟨by norm_num, fun m hm hdvd => by
      rcases Math.divisors_13 m hdvd with h | h
      · exact h
      · omega⟩), 2, 3, by norm_num⟩

end Math

/-!
# Two Squares 13
Category: Pure Mathematics
Target: Math.two_squares_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean 4 requires `import` commands to precede every other command in a file,
including module doc comments such as the mandated header above.  Since the header
must literally begin the file, this development is carried out in pure core Lean,
without importing Mathlib; primality of 13 is therefore spelled out explicitly
(`2 ≤ 13` together with the fact that every divisor of 13 is `1` or `13`).
-/

namespace Math

/-- Every divisor of `13` is `1` or `13`. -/
theorem divisors_13 : ∀ m : Nat, m ∣ 13 → m = 1 ∨ m = 13 := by
  have key : ∀ m : Nat, m < 14 → m ∣ 13 → m = 1 ∨ m = 13 := by decide
  intro m hm
  exact key m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

/-- **Two squares for 13.** The number `13` is prime (it is at least `2` and its only
divisors are `1` and itself) and it is a sum of two squares, namely `13 = 2 ^ 2 + 3 ^ 2`. -/
theorem two_squares_13 :
    (2 ≤ 13 ∧ ∀ m : Nat, m ∣ 13 → m = 1 ∨ m = 13) ∧ ∃ a b : Nat, 13 = a ^ 2 + b ^ 2 :=
  ⟨⟨by decide, divisors_13⟩, 2, 3, by decide⟩

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

