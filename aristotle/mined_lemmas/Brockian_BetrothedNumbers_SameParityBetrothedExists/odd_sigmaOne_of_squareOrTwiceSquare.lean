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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to be the very first command in a file, so the header module
-- docstring above sits immediately after the single `import Mathlib` line.)

namespace Brockian
namespace BetrothedNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

theorem odd_sigmaOne_of_squareOrTwiceSquare {n : ℕ} (hn : n ≠ 0) (h : SquareOrTwiceSquare n) :
    Odd (sigmaOne n) := by
  have hodd : ∀ p, p ≠ 2 → Even (n.factorization p) := by
    intro p hp
    rcases h with hsq | ⟨j, hj⟩
    · exact even_factorization_of_isSquare hn hsq p
    · have hj0 : j ≠ 0 := by rintro rfl; simp at hj; exact hn hj
      subst hj
      rw [Nat.factorization_mul two_ne_zero (pow_ne_zero 2 hj0)]
      simp [Nat.Prime.factorization Nat.prime_two, Ne.symm hp, Nat.factorization_pow]
  set k := n.factorization 2 with hk
  set m := ordCompl[2] n with hmdef
  have hsplit : 2 ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl Nat.prime_two hn)
  have hmodd : Odd m := Nat.odd_iff.mpr (by
    have := Nat.not_dvd_ordCompl Nat.prime_two hn
    omega)
  have hm0 : m ≠ 0 := by rintro h0; rw [h0] at hmodd; simp at hmodd
  have hmsq : IsSquare m := by
    refine isSquare_of_factorization_even hm0 fun p => ?_
    rw [hmdef, Nat.factorization_ordCompl]
    by_cases hp : p = 2
    · subst hp; simp
    · rw [Finsupp.erase_ne hp]; exact hodd p hp
  rw [← hsplit, sigmaOne_mul_of_coprime hcop]
  exact (odd_sigmaOne_two_pow k).mul (odd_sigmaOne_of_odd_isSquare hmodd hmsq)

/-- **Characterization.** A nonzero natural number has odd sum of divisors if and only if it is
a square or twice a square. -/
