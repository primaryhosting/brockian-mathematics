/-!
# Quadruplet 11 13 17 19
Category: Frontier — Prime Numbers
Target: Constellation.quadruplet_11_13_17_19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Constellation

/-- Primality of a natural number: `n` is at least `2` and its only divisors are `1` and `n`.

This file is required to begin with the header comment above, which Lean parses as a module
documentation command; consequently no `import` line may follow it, so the development below is
carried out with the Lean core library only, and primality is spelled out explicitly here
(this predicate is equivalent to Mathlib's `Nat.Prime`). -/
def IsPrime (n : Nat) : Prop := 2 ≤ n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

/-- A finite criterion for primality: it suffices to check the divisors below `n + 1`. -/
theorem isPrime_of_bounded (n : Nat) (h2 : 2 ≤ n)
    (h : ∀ m, m < n + 1 → m ∣ n → m = 1 ∨ m = n) : IsPrime n := by
  refine ⟨h2, fun m hm => h m ?_ hm⟩
  have := Nat.le_of_dvd (by omega) hm
  omega

theorem isPrime_eleven : IsPrime 11 := isPrime_of_bounded 11 (by decide) (by decide)

theorem isPrime_thirteen : IsPrime 13 := isPrime_of_bounded 13 (by decide) (by decide)

theorem isPrime_seventeen : IsPrime 17 := isPrime_of_bounded 17 (by decide) (by decide)

theorem isPrime_nineteen : IsPrime 19 := isPrime_of_bounded 19 (by decide) (by decide)

/-- `(11, 13, 17, 19)` is a prime quadruplet of pattern `(0, 2, 6, 8)`: all four numbers are
prime, and `13 = 11 + 2`, `17 = 11 + 6`, `19 = 11 + 8`. -/
theorem quadruplet_11_13_17_19 :
    IsPrime 11 ∧ IsPrime 13 ∧ IsPrime 17 ∧ IsPrime 19 ∧
      13 = 11 + 2 ∧ 17 = 11 + 6 ∧ 19 = 11 + 8 :=
  ⟨isPrime_eleven, isPrime_thirteen, isPrime_seventeen, isPrime_nineteen, rfl, rfl, rfl⟩

end Constellation

import Mathlib
import RequestProject.Quadruplet11131719

/-!
# Bridge to Mathlib's `Nat.Prime`

The main file `RequestProject/Quadruplet11131719.lean` is required to begin with a fixed header
comment, which Lean parses as a module documentation command; no `import` may follow it, so the
target theorem there is stated with the self-contained predicate `Constellation.IsPrime`.

Here we check that this predicate agrees with Mathlib's `Nat.Prime`, and restate the quadruplet
result in Mathlib terms.
-/

namespace Constellation

/-- The self-contained predicate `Constellation.IsPrime` agrees with Mathlib's `Nat.Prime`. -/
theorem isPrime_iff_nat_prime (n : ℕ) : IsPrime n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨h2, h⟩
    refine Nat.prime_def.mpr ⟨h2, fun m hm => ?_⟩
    rcases h m hm with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro hp
    exact ⟨hp.two_le, fun m hm => (Nat.Prime.eq_one_or_self_of_dvd hp m hm)⟩

/-- `(11, 13, 17, 19)` is a prime quadruplet of pattern `(0, 2, 6, 8)`, stated with Mathlib's
`Nat.Prime`. -/
theorem quadruplet_11_13_17_19_natPrime :
    Nat.Prime 11 ∧ Nat.Prime 13 ∧ Nat.Prime 17 ∧ Nat.Prime 19 ∧
      13 = 11 + 2 ∧ 17 = 11 + 6 ∧ 19 = 11 + 8 :=
  ⟨(isPrime_iff_nat_prime 11).mp isPrime_eleven,
   (isPrime_iff_nat_prime 13).mp isPrime_thirteen,
   (isPrime_iff_nat_prime 17).mp isPrime_seventeen,
   (isPrime_iff_nat_prime 19).mp isPrime_nineteen, rfl, rfl, rfl⟩

end Constellation

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

