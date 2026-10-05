/-!
# Two Squares 101
Category: Pure Mathematics
Target: Math.two_squares_101
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean 4 requires `import` commands to be the very first commands in a
file, so no `import` line may precede the header comment above.  This file is therefore
written to be self-contained (no imports at all): primality of `101` is stated directly
as the divisor characterisation `∀ m, m ∣ 101 → m = 1 ∨ m = 101` (together with
`1 < 101`).  The companion file `RequestProject/Main.lean` restates the result using
Mathlib's `Nat.Prime` predicate, deriving it from the theorem below.
-/

namespace Math

/-- **Two squares for 101.**  The number `101` is prime — its only divisors are `1`
and `101`, and `1 < 101` — and it is a sum of two squares, namely `101 = 1 ^ 2 + 10 ^ 2`. -/
theorem two_squares_101 :
    (1 < 101 ∧ ∀ m : Nat, m ∣ 101 → m = 1 ∨ m = 101) ∧
      ∃ a b : Nat, 101 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 1, 10, rfl⟩
  intro m hm
  have hle : m ≤ 101 := Nat.le_of_dvd (by decide) hm
  have h : ∀ k : Nat, k < 102 → k ∣ 101 → k = 1 ∨ k = 101 := by decide
  exact h m (Nat.lt_succ_of_le hle) hm

end Math

import Mathlib
import RequestProject.TwoSquares101

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
# Two Squares 101
Category: Pure Mathematics
Target: Math.two_squares_101
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Mathlib-flavoured restatement of `Math.two_squares_101`
(see `RequestProject/TwoSquares101.lean`).
-/

namespace Math

/-- The prime `101` is a sum of two squares: `101 = 1 ^ 2 + 10 ^ 2`. -/
theorem two_squares_101_prime : Nat.Prime 101 ∧ ∃ a b : ℕ, 101 = a ^ 2 + b ^ 2 :=
  ⟨Nat.prime_def.mpr Math.two_squares_101.1, Math.two_squares_101.2⟩

end Math

