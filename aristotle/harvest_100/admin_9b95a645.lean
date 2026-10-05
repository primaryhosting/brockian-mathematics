/-!
# Two Squares 113
Category: Pure Mathematics
Target: Math.two_squares_113
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **113 is a prime that is a sum of two squares.**

The statement is spelled out without any imports (so that the required header comment can
be the very first thing in the file): primality of `113` is stated in its unfolded form
`1 < 113 ∧ ∀ m, m ∣ 113 → m = 1 ∨ m = 113`, which is exactly `Nat.Prime 113`
(cf. `Nat.prime_def`), and the two-squares part is witnessed explicitly by `113 = 7 ^ 2 + 8 ^ 2`.

The existence of such a representation also follows abstractly from Mathlib's
`Nat.Prime.sq_add_sq` (every prime `p` with `p % 4 ≠ 3` is a sum of two squares),
since `113 % 4 = 1`. -/
theorem two_squares_113 :
    (1 < 113 ∧ ∀ m : Nat, m ∣ 113 → m = 1 ∨ m = 113) ∧ ∃ a b : Nat, a ^ 2 + b ^ 2 = 113 := by
  refine ⟨⟨by decide, ?_⟩, 7, 8, by decide⟩
  have key : ∀ m ≤ 113, m ∣ 113 → m = 1 ∨ m = 113 := by decide
  exact fun m hm => key m (Nat.le_of_dvd (by decide) hm) hm

end Math

import Mathlib
import RequestProject.Math

/-!
# Two Squares 113 — Mathlib-flavoured restatement

`Math.two_squares_113` is stated in `RequestProject/Math.lean` without imports (its header
comment must be the first thing in that file). Here we record that its primality component is
literally `Nat.Prime 113`.
-/

namespace Math

/-- `113` is prime and is a sum of two squares, stated with Mathlib's `Nat.Prime`. -/
theorem two_squares_113_prime : Nat.Prime 113 ∧ ∃ a b : ℕ, a ^ 2 + b ^ 2 = 113 := by
  obtain ⟨⟨h1, h2⟩, hsq⟩ := two_squares_113
  exact ⟨Nat.prime_def.mpr ⟨h1, h2⟩, hsq⟩

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

