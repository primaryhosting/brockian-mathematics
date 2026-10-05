import Mathlib
import RequestProject.TwoSquares5

/-!
# Two Squares 5 — link with Mathlib

`RequestProject/TwoSquares5.lean` must begin with a prescribed header comment, so it
cannot contain an `import` line and is stated with a self-contained primality
predicate `Math.IsPrimeNat`.  Here we check that this predicate is exactly
Mathlib's `Nat.Prime`, and restate the main result in Mathlib terms.
-/

namespace Math

/-- The self-contained primality predicate agrees with Mathlib's `Nat.Prime`. -/
theorem isPrimeNat_iff_prime (n : Nat) : IsPrimeNat n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨h2, hdvd⟩
    refine Nat.prime_def.mpr ⟨h2, fun m hm => ?_⟩
    rcases hdvd m hm with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro hp
    exact ⟨hp.two_le, fun m hm => (Nat.Prime.eq_one_or_self_of_dvd hp m hm)⟩

/-- The prime `5` is a sum of two squares, stated with Mathlib's `Nat.Prime`. -/
theorem two_squares_5' : Nat.Prime 5 ∧ ∃ a b : Nat, 5 = a ^ 2 + b ^ 2 :=
  ⟨(isPrimeNat_iff_prime 5).mp two_squares_5.1, two_squares_5.2⟩

end Math

/-!
# Two Squares 5
Category: Pure Mathematics
Target: Math.two_squares_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `IsPrimeNat n` says that `n` is a prime natural number: it is at least `2`,
and its only divisors are `1` and itself.  (This is stated self-containedly so
that this file can begin with the required header comment; the file
`TwoSquares5Mathlib.lean` proves that it agrees with Mathlib's `Nat.Prime`.) -/
def IsPrimeNat (n : Nat) : Prop :=
  2 ≤ n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

/-- **Two squares for 5.**  The number `5` is prime and is a sum of two squares,
namely `5 = 1 ^ 2 + 2 ^ 2`.

Equivalent reformulation used in the proof: instead of quantifying over all
divisors of `5`, it suffices to check the finitely many candidates `m ≤ 5`,
since every divisor of `5` is at most `5`. -/
theorem two_squares_5 : IsPrimeNat 5 ∧ ∃ a b : Nat, 5 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, fun m hm => ?_⟩, 1, 2, by decide⟩
  have hle : m ≤ 5 := Nat.le_of_dvd (by decide) hm
  have key : ∀ k, k ≤ 5 → k ∣ 5 → k = 1 ∨ k = 5 := by decide
  exact key m hle hm

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

