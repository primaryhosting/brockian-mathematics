import Mathlib
import RequestProject.TwoSquares5

/-!
# Two Squares 5 (Mathlib phrasing)

A restatement of `Math.two_squares_5` using Mathlib's `Nat.Prime`, together with a proof that the
explicit primality condition appearing in `Math.two_squares_5` really is `Nat.Prime 5`.
-/

namespace Math

/-- The prime `5` is a sum of two squares: `5 = 1 ^ 2 + 2 ^ 2`. -/
theorem two_squares_5_nat_prime : Nat.Prime 5 ∧ ∃ a b : ℕ, 5 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 1, 2, by norm_num⟩

/-- The explicit primality condition used in `Math.two_squares_5` is exactly `Nat.Prime 5`. -/
theorem two_squares_5_prime_spec :
    (2 ≤ 5 ∧ ∀ m : ℕ, m ∣ 5 → m = 1 ∨ m = 5) ↔ Nat.Prime 5 :=
  (Nat.prime_def (p := 5)).symm

/-- `Math.two_squares_5` restated with Mathlib's `Nat.Prime`, derived from the import-free version. -/
theorem two_squares_5_mathlib : Nat.Prime 5 ∧ ∃ a b : ℕ, 5 = a ^ 2 + b ^ 2 :=
  ⟨two_squares_5_prime_spec.mp two_squares_5.1, two_squares_5.2⟩

end Math

/-!
# Two Squares 5
Category: Pure Mathematics
Target: Math.two_squares_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/--
**The prime `5` is a sum of two squares.**

The statement asserts both that `5` is prime (spelled out as: `2 ≤ 5` and every divisor of `5`
is `1` or `5`) and that `5 = 1 ^ 2 + 2 ^ 2`.

Primality is written out explicitly rather than via `Nat.Prime` so that this file, which must
begin with the required header comment, needs no `import` line (Lean requires imports to be the
very first commands in a file).  A Mathlib-phrased version using `Nat.Prime` is given in
`RequestProject/TwoSquares5Mathlib.lean`.

The proof of the divisor condition is the contrapositive-style reformulation suggested: instead of
reasoning about primality abstractly, we note that any divisor `m` of `5` satisfies `m ≤ 5` and
`5 % m = 0`, which leaves only finitely many cases to check.
-/
theorem two_squares_5 :
    (2 ≤ 5 ∧ ∀ m : Nat, m ∣ 5 → m = 1 ∨ m = 5) ∧ ∃ a b : Nat, 5 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 1, 2, by decide⟩
  intro m hm
  have h : m ≤ 5 := Nat.le_of_dvd (by decide) hm
  have h0 : 5 % m = 0 := Nat.dvd_iff_mod_eq_zero.mp hm
  match m, h, h0 with
  | 0, _, h0 => exact absurd h0 (by decide)
  | 1, _, _ => exact Or.inl rfl
  | 2, _, h0 => exact absurd h0 (by decide)
  | 3, _, h0 => exact absurd h0 (by decide)
  | 4, _, h0 => exact absurd h0 (by decide)
  | 5, _, _ => exact Or.inr rfl
  | (_ + 6), h, _ => exact absurd h (by omega)

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

