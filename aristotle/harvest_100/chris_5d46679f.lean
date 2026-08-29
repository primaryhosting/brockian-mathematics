import Mathlib
import RequestProject.TwoSquares109

/-!
# Two Squares 109 — Mathlib phrasing

Restatement of `Math.two_squares_109` using Mathlib's `Nat.Prime`.
-/

namespace Math

/-- The prime `109` is a sum of two squares: `109 = 10 ^ 2 + 3 ^ 2`. -/
theorem two_squares_109_prime : Nat.Prime 109 ∧ ∃ a b : ℕ, 109 = a ^ 2 + b ^ 2 :=
  ⟨Nat.prime_def.mpr ⟨by omega, fun m hm => two_squares_109.1.2 m hm⟩, two_squares_109.2⟩

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
# Two Squares 109
Category: Pure Mathematics
Target: Math.two_squares_109
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 109.**  The number `109` is prime — here primality is spelled out
directly as `2 ≤ 109` together with the statement that every divisor of `109` is `1` or
`109` — and it is a sum of two squares, namely `109 = 10 ^ 2 + 3 ^ 2`.

This file is deliberately self-contained (no imports), since the required header comment
is a module docstring and must be the very first item in the file.  A statement phrased
with Mathlib's `Nat.Prime` is proved in `RequestProject/TwoSquares109Mathlib.lean`. -/
theorem two_squares_109 :
    (2 ≤ 109 ∧ ∀ m : Nat, m ∣ 109 → m = 1 ∨ m = 109) ∧ ∃ a b : Nat, 109 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by omega, ?_⟩, 10, 3, by rfl⟩
  have key : ∀ m : Nat, m < 109 → m = 1 ∨ ¬ (109 % m = 0) := by decide
  intro m hm
  have hle : m ≤ 109 := Nat.le_of_dvd (by omega) hm
  rcases Nat.lt_or_ge m 109 with h | h
  · rcases key m h with h1 | h1
    · exact Or.inl h1
    · exact absurd (Nat.dvd_iff_mod_eq_zero.mp hm) h1
  · exact Or.inr (by omega)

end Math

