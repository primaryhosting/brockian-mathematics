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

import Mathlib

/-!
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FermatNumbers

private instance factPrimeThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The Pépin condition for the `n`-th Fermat number `Fₙ = 2 ^ 2 ^ n + 1`:
`3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`. -/

theorem pepinCondition_of_prime (n : ℕ) (hn : 1 ≤ n) (hp : Nat.Prime (Nat.fermatNumber n)) :
    PepinCondition n := by
  haveI : Fact (Nat.Prime (Nat.fermatNumber n)) := ⟨hp⟩
  have hhalf : Nat.fermatNumber n / 2 = 2 ^ (2 ^ n - 1) := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h : (2 : ℕ) ^ 2 ^ n = 2 * 2 ^ (2 ^ n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    simp [Nat.fermatNumber, h, Nat.mul_add_div]
  have heuler : ((legendreSym (Nat.fermatNumber n) 3 : ℤ) : ZMod (Nat.fermatNumber n))
      = ((3 : ℤ) : ZMod (Nat.fermatNumber n)) ^ (Nat.fermatNumber n / 2) :=
    legendreSym.eq_pow (Nat.fermatNumber n) 3
  rw [legendreSym_three_fermatNumber n hn ⟨hp⟩, hhalf] at heuler
  unfold PepinCondition
  push_cast at heuler
  exact heuler.symm

/-- **Pépin's test**: for `n ≥ 1`, the Fermat number `Fₙ` is prime if and only if the Pépin
condition holds. -/
