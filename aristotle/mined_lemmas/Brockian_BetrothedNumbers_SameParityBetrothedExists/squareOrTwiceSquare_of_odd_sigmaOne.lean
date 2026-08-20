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

theorem squareOrTwiceSquare_of_odd_sigmaOne {n : ℕ} (hn : n ≠ 0) (h : Odd (sigmaOne n)) :
    SquareOrTwiceSquare n := by
  set k := n.factorization 2 with hk
  set m := ordCompl[2] n with hmdef
  have hsplit : 2 ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl Nat.prime_two hn)
  have hmodd : Odd m := Nat.odd_iff.mpr (by
    have := Nat.not_dvd_ordCompl Nat.prime_two hn
    omega)
  have hprod : sigmaOne n = sigmaOne (2 ^ k) * sigmaOne m := by
    rw [← hsplit, sigmaOne_mul_of_coprime hcop]
  have hoddm : Odd (sigmaOne m) := by
    rw [hprod] at h
    exact (Nat.odd_mul.mp h).2
  obtain ⟨j, hj⟩ := isSquare_of_odd_of_odd_sigmaOne hmodd hoddm
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨t, ht⟩ := he
    left
    refine ⟨2 ^ t * j, ?_⟩
    rw [← hsplit, hj, ht, pow_add]
    ring
  · obtain ⟨t, ht⟩ := ho
    right
    refine ⟨2 ^ t * j, ?_⟩
    rw [← hsplit, hj, ht, mul_pow, ← pow_mul]
    ring

/-! ### The converse: a full characterization of numbers with odd divisor sum -/

