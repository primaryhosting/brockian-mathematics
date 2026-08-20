import Mathlib
import RequestProject.TwoSquares97

/-!
# Two Squares 97 — Mathlib form

Restatement of `Math.two_squares_97` using Mathlib's `Nat.Prime`.
-/

namespace Math

/-- The prime `97` is a sum of two squares: `97 = 4 ^ 2 + 9 ^ 2`. -/
theorem two_squares_97_prime : Nat.Prime 97 ∧ ∃ a b : ℕ, 97 = a ^ 2 + b ^ 2 :=
  ⟨Nat.prime_def.mpr two_squares_97.1, two_squares_97.2⟩

end Math

/-!
# Two Squares 97
Category: Pure Mathematics
Target: Math.two_squares_97
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean 4 requires `import` commands to precede every other command,
including module doc comments, so this file (which must begin with the header above)
is written using only Lean core.  Primality of `97` is therefore spelled out
explicitly as `1 < 97 ∧ ∀ m, m ∣ 97 → m = 1 ∨ m = 97`, which is exactly Mathlib's
`Nat.Prime` characterisation (`Nat.prime_def`); the file
`RequestProject/TwoSquares97Mathlib.lean` derives the `Nat.Prime 97` form from this one.
-/

namespace Math

/-- **Two squares for 97.** The number `97` is prime (stated as: `1 < 97` and every
divisor of `97` is `1` or `97`) and is a sum of two squares, namely `97 = 4 ^ 2 + 9 ^ 2`. -/
theorem two_squares_97 :
    (1 < 97 ∧ ∀ m : Nat, m ∣ 97 → m = 1 ∨ m = 97) ∧ ∃ a b : Nat, 97 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 4, 9, rfl⟩
  intro m hm
  have h1 : m ≤ 97 := Nat.le_of_dvd (by decide) hm
  revert hm
  revert h1
  revert m
  decide

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

