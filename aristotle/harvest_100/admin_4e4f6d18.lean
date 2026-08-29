import Mathlib
import RequestProject.TwoSquares5

/-!
# Two Squares 5 — Mathlib phrasing

The statement of `Math.two_squares_5` phrased with Mathlib's `Nat.Prime`, together with the
derivation of the Mathlib phrasing from the elementary one.
-/

namespace Math

/-- The prime `5` is a sum of two squares, phrased with Mathlib's `Nat.Prime`. -/
theorem two_squares_5_prime : Nat.Prime 5 ∧ ∃ a b : ℕ, 5 = a ^ 2 + b ^ 2 := by
  obtain ⟨⟨h1, hdvd⟩, hsq⟩ := two_squares_5
  exact ⟨Nat.prime_def.mpr ⟨h1, hdvd⟩, hsq⟩

end Math

/-!
# Two Squares 5
Category: Pure Mathematics
Target: Math.two_squares_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **The prime 5 is a sum of two squares.**

The number `5` is prime (it is greater than `1` and its only divisors are `1` and `5`)
and it is a sum of two squares, namely `5 = 1 ^ 2 + 2 ^ 2`.

(The primality predicate is spelled out explicitly here rather than via `Nat.Prime`, since
the required file header must be the first command in the file, which precludes an `import`
line; the equivalent statement phrased with Mathlib's `Nat.Prime` is
`Math.two_squares_5_prime` in `RequestProject/TwoSquares5Mathlib.lean`.) -/
theorem two_squares_5 :
    (1 < 5 ∧ ∀ d : Nat, d ∣ 5 → d = 1 ∨ d = 5) ∧ ∃ a b : Nat, 5 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by omega, ?_⟩, 1, 2, by decide⟩
  intro d hd
  have h1 := Nat.le_of_dvd (by omega) hd
  match d, h1, hd with
  | 0, _, h => exact absurd h (by decide)
  | 1, _, _ => exact Or.inl rfl
  | 2, _, h => exact absurd h (by decide)
  | 3, _, h => exact absurd h (by decide)
  | 4, _, h => exact absurd h (by decide)
  | 5, _, _ => exact Or.inr rfl
  | (n + 6), h, _ => omega

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

