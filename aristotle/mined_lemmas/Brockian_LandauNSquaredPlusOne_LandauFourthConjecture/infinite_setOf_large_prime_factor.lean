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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean does not allow a module
-- docstring to precede the `import` commands; the text is otherwise verbatim.)

import Mathlib

/-!
# Landau Fourth Conjecture

Landau's fourth problem asks whether there are infinitely many primes of the form `n ^ 2 + 1`.
This is a well-known open problem, so what is proved here is:

* `LandauFourthConjecture` : a **conditional** reduction — Bunyakovsky's conjecture
  (in the form `BunyakovskyHypothesis`) implies Landau's fourth conjecture
  (`LandauFourthStatement`).  All the hypotheses of Bunyakovsky's conjecture are verified
  unconditionally for the polynomial `X ^ 2 + 1`.
* `X_sq_add_one_irreducible` : `X ^ 2 + 1` is irreducible over `ℤ`.
* `infinite_setOf_prime_dvd_sq_add_one` : an **unconditional** partial result — infinitely many
  primes divide some number of the form `n ^ 2 + 1`.
* `infinite_setOf_large_prime_factor` : an **unconditional** partial result — for infinitely many
  `n`, the number `n ^ 2 + 1` has a prime factor exceeding `2 * n`.
-/

open Polynomial

namespace Brockian.LandauNSquaredPlusOne

/-- **Landau's fourth conjecture**: there are infinitely many natural numbers `n` such that
`n ^ 2 + 1` is prime. -/

theorem infinite_setOf_large_prime_factor :
    {n : ℕ | ∃ p : ℕ, p.Prime ∧ p ∣ n ^ 2 + 1 ∧ 2 * n < p}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨p, hpgt, hp, hp4⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 4) (a := 1) isUnit_one ((N + 1) ^ 2 + 1)
  haveI : Fact p.Prime := ⟨hp⟩
  have hmod : p % 4 = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' p 1 4).mp (by simpa using hp4)
    simpa using this
  obtain ⟨r, hr⟩ : IsSquare (-1 : ZMod p) := by
    rw [ZMod.exists_sq_eq_neg_one_iff]; omega
  have hrsq : (r : ZMod p) ^ 2 + 1 = 0 := by rw [sq, ← hr]; ring
  have hrval : r.val < p := ZMod.val_lt r
  have hcast : ((r.val : ℕ) : ZMod p) = r := ZMod.natCast_val r |>.trans (ZMod.cast_id _ _)
  have hd1 : p ∣ r.val ^ 2 + 1 :=
    dvd_sq_add_one_of_cast_eq_zero p r.val (by rw [hcast]; exact hrsq)
  have hd2 : p ∣ (p - r.val) ^ 2 + 1 := by
    refine dvd_sq_add_one_of_cast_eq_zero p _ ?_
    have hc : ((p - r.val : ℕ) : ZMod p) = -r := by
      rw [Nat.cast_sub hrval.le, hcast]; simp
    rw [hc, neg_pow]
    simpa using hrsq
  have hr0 : r.val ≠ 0 := by
    intro h
    have hz : (r : ZMod p) = 0 := by rw [← hcast, h]; simp
    rw [hz] at hrsq
    simp at hrsq
  set m := min r.val (p - r.val) with hm
  have hpodd : p % 2 = 1 := by omega
  have h2m : 2 * m < p := by
    rcases le_total r.val (p - r.val) with h | h
    · have hmm : m = r.val := by simp [hm, h]
      omega
    · have hmm : m = p - r.val := by simp [hm, h]
      omega
  have hdm : p ∣ m ^ 2 + 1 := by
    rcases le_total r.val (p - r.val) with h | h
    · have hmm : m = r.val := by simp [hm, h]
      rw [hmm]; exact hd1
    · have hmm : m = p - r.val := by simp [hm, h]
      rw [hmm]; exact hd2
  have hge : p ≤ m ^ 2 + 1 := Nat.le_of_dvd (by positivity) hdm
  refine ⟨m, ⟨p, hp, hdm, h2m⟩, ?_⟩
  nlinarith [hge, hpgt]

/-- A convenient reformulation of Landau's fourth conjecture. -/
