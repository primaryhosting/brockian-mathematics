import Mathlib
import RequestProject.TwoSquares53

/-!
# Two Squares 53 — Mathlib restatement

The target theorem `Math.two_squares_53` lives in `RequestProject/TwoSquares53.lean`,
which is import-free (its statement uses the self-contained predicate `Math.IsPrimeNat`).
Here we record that this predicate agrees with Mathlib's `Nat.Prime`, and restate the
result in Mathlib terms.
-/

namespace Math

/-- `Math.IsPrimeNat` agrees with Mathlib's `Nat.Prime`. -/
theorem isPrimeNat_iff_prime (n : Nat) : IsPrimeNat n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨h2, hd⟩
    refine Nat.prime_def.mpr ⟨h2, fun m hm => ?_⟩
    exact hd m hm
  · intro hp
    exact ⟨hp.two_le, fun m hm => (Nat.Prime.eq_one_or_self_of_dvd hp m hm)⟩

/-- The prime `53` is a sum of two squares, stated with Mathlib's `Nat.Prime`. -/
theorem two_squares_53' : Nat.Prime 53 ∧ ∃ a b : ℕ, 53 = a ^ 2 + b ^ 2 :=
  ⟨(isPrimeNat_iff_prime 53).mp prime_53, 7, 2, by norm_num⟩

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
# Two Squares 53
Category: Pure Mathematics
Target: Math.two_squares_53
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Primality of a natural number, stated without any imports:
`n` is at least `2` and its only divisors are `1` and `n`. -/
def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

/-- Every divisor of `53` is `1` or `53` (checked by decision procedure on the
finitely many candidates `m ≤ 53`, using that a divisor of a positive number
is at most that number). -/
theorem divisors_53 : ∀ m, m ∣ 53 → m = 1 ∨ m = 53 := by
  have key : ∀ m ≤ 53, m ∣ 53 → m = 1 ∨ m = 53 := by decide
  intro m hm
  exact key m (Nat.le_of_dvd (by decide) hm) hm

/-- `53` is prime. -/
theorem prime_53 : IsPrimeNat 53 := ⟨by decide, divisors_53⟩

/-- **Two squares for 53**: the prime `53` is a sum of two squares,
namely `53 = 7 ^ 2 + 2 ^ 2`. -/
theorem two_squares_53 : IsPrimeNat 53 ∧ ∃ a b : Nat, 53 = a ^ 2 + b ^ 2 :=
  ⟨prime_53, 7, 2, by decide⟩

end Math

