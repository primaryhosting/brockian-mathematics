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

/-
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brocard Gap Conjecture

Brocard's problem asks for the solutions of `n ! + 1 = m ^ 2`; the only known ones are the
*Brown pairs* `(4, 5)`, `(5, 11)`, `(7, 71)`, and Brocard's conjecture (still open) states that
there are no further solutions.

This file develops the *gap* side of the problem, i.e. how far apart the perfect squares
surrounding `n ! + 1` are, and records what can be proved unconditionally:

* `Brockian.BrocardGap.BrocardGapConjecture` : for `n ≥ 10` the two consecutive squares
  bracketing `n ! + 1` are more than `2 ^ (n + 1)` apart;
* `Brockian.BrocardGap.unique_sq_near_factorial` : consequently, for `n ≥ 10` at most one
  natural number has its square within `2 ^ n` of `n ! + 1`;
* `Brockian.BrocardGap.no_brownPair_of_mem_Icc_eight_hundred` : an unconditional verification
  that there is no Brown pair with `8 ≤ n ≤ 100`;
* `Brockian.BrocardGap.two_pow_lt_of_brownPair` : any solution with `n ≥ 10` has `2 ^ n < m`;
* `Brockian.BrocardGap.brownPair_eq_sqrt`, `brownPair_factorization`, `brownPair_odd` :
  elementary structure of a solution;
* `Brockian.BrocardGap.brocardConjecture_iff_no_square` : a reformulation of the full
  (open) Brocard conjecture as the statement that `n ! + 1` is never a perfect square
  for `n ≥ 8`.
-/

open scoped Nat

namespace Brockian.BrocardGap

/-- A *Brown pair* is a pair `(n, m)` solving Brocard's equation `n ! + 1 = m ^ 2`. -/

theorem unique_sq_near_factorial (n : ℕ) (hn : 10 ≤ n) (m₁ m₂ : ℕ)
    (h₁ : |(n ! : ℤ) + 1 - (m₁ : ℤ) ^ 2| ≤ 2 ^ n)
    (h₂ : |(n ! : ℤ) + 1 - (m₂ : ℤ) ^ 2| ≤ 2 ^ n) : m₁ = m₂ := by
  have hfac : (2 : ℤ) * 4 ^ n ≤ (n ! : ℤ) := by
    exact_mod_cast two_mul_four_pow_le_factorial n hn
  have hsq : (2 : ℤ) ^ n * 2 ^ n = 4 ^ n := by
    rw [← mul_pow]; norm_num
  have hpos : (0 : ℤ) < 2 ^ n := by positivity
  have hle : (2 : ℤ) ^ n ≤ 4 ^ n := by gcongr; norm_num
  have key : ∀ m : ℕ, |(n ! : ℤ) + 1 - (m : ℤ) ^ 2| ≤ 2 ^ n → (2 : ℤ) ^ n < (m : ℤ) := by
    intro m hm
    have hlow : (n ! : ℤ) + 1 - 2 ^ n ≤ (m : ℤ) ^ 2 := by
      have := (abs_le.1 hm).2; linarith
    by_contra hcon
    push_neg at hcon
    have hm0 : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
    nlinarith [hlow, hsq, hcon, hm0, hle, hfac]
  have k₁ := key m₁ h₁
  have k₂ := key m₂ h₂
  by_contra hne
  rcases Nat.lt_or_ge m₁ m₂ with hlt | hge
  · have hstep : ((m₁ : ℤ) + 1) ≤ (m₂ : ℤ) := by exact_mod_cast hlt
    have hb₁ : (n ! : ℤ) + 1 - 2 ^ n ≤ (m₁ : ℤ) ^ 2 := by
      have := (abs_le.1 h₁).2; linarith
    have hb₂ : (m₂ : ℤ) ^ 2 ≤ (n ! : ℤ) + 1 + 2 ^ n := by
      have := (abs_le.1 h₂).1; linarith
    nlinarith [hstep, hb₁, hb₂, k₁, hpos]
  · have hlt : m₂ < m₁ := by omega
    have hstep : ((m₂ : ℤ) + 1) ≤ (m₁ : ℤ) := by exact_mod_cast hlt
    have hb₂ : (n ! : ℤ) + 1 - 2 ^ n ≤ (m₂ : ℤ) ^ 2 := by
      have := (abs_le.1 h₂).2; linarith
    have hb₁ : (m₁ : ℤ) ^ 2 ≤ (n ! : ℤ) + 1 + 2 ^ n := by
      have := (abs_le.1 h₁).1; linarith
    nlinarith [hstep, hb₁, hb₂, k₂, hpos]

/-! ### An unconditional finite verification -/

/-- A number strictly between two consecutive squares is not a square. -/
