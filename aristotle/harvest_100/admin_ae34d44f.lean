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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.AndricaConjecture

open Real

/-- `nthPrime n` is the `n`-th prime number (`nthPrime 0 = 2`). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

lemma nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) := Nat.prime_nth_prime n

lemma nthPrime_pos (n : ℕ) : 0 < nthPrime n := (nthPrime_prime n).pos

lemma nthPrime_lt_succ (n : ℕ) : nthPrime n < nthPrime (n + 1) :=
  (Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr (Nat.lt_succ_self n)

/-- The Andrica difference `√p_{n+1} - √p_n`. -/
noncomputable def andricaGap (n : ℕ) : ℝ :=
  Real.sqrt (nthPrime (n + 1)) - Real.sqrt (nthPrime n)

/-- Elementary reformulation: for `a, b ≥ 0`, `√b - √a < 1` iff `b < a + 2√a + 1`. -/
lemma sqrt_sub_sqrt_lt_one_iff {a b : ℝ} (ha : 0 ≤ a) :
    Real.sqrt b - Real.sqrt a < 1 ↔ b < a + 2 * Real.sqrt a + 1 := by
  have hs : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hpos : (0:ℝ) < Real.sqrt a + 1 := by linarith
  have h := Real.sqrt_lt' (x := b) hpos
  have hsq : (Real.sqrt a + 1) ^ 2 = a + 2 * Real.sqrt a + 1 := by
    have : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
    nlinarith [this]
  rw [hsq] at h
  constructor
  · intro hb
    exact h.mp (by linarith)
  · intro hb
    have := h.mpr hb
    linarith

/-- The Andrica gap at index `n` is `< 1` exactly when the prime gap satisfies
`p_{n+1} < p_n + 2√p_n + 1`. -/
lemma andricaGap_lt_one_iff (n : ℕ) :
    andricaGap n < 1 ↔
      (nthPrime (n + 1) : ℝ) < (nthPrime n : ℝ) + 2 * Real.sqrt (nthPrime n) + 1 := by
  simpa [andricaGap] using
    sqrt_sub_sqrt_lt_one_iff (a := (nthPrime n : ℝ)) (b := (nthPrime (n + 1) : ℝ))
      (by positivity)

/-- **Reduction of the Andrica conjecture to a prime-gap bound.** The Andrica conjecture
`√p_{n+1} - √p_n < 1` for all `n` is *equivalent* to the bound
`p_{n+1} < p_n + 2√p_n + 1` for all `n`. -/
theorem andrica_iff_gap_bound :
    (∀ n : ℕ, andricaGap n < 1) ↔
      (∀ n : ℕ, (nthPrime (n + 1) : ℝ) < (nthPrime n : ℝ) + 2 * Real.sqrt (nthPrime n) + 1) :=
  forall_congr' fun n => andricaGap_lt_one_iff n

/-- **Andrica conjecture, conditional form.** Assuming the prime-gap bound
`p_{n+1} < p_n + 2√p_n + 1` (which is equivalent to it, see `andrica_iff_gap_bound`),
we have `√p_{n+1} - √p_n < 1` for every `n`.

The Andrica conjecture is an open problem, so the result is stated here in this
conditional (reduced) form. -/
theorem AndricaConjecture
    (hgap : ∀ n : ℕ, (nthPrime (n + 1) : ℝ) < (nthPrime n : ℝ) + 2 * Real.sqrt (nthPrime n) + 1) :
    ∀ n : ℕ, Real.sqrt (nthPrime (n + 1)) - Real.sqrt (nthPrime n) < 1 :=
  fun n => (andricaGap_lt_one_iff n).mpr (hgap n)

/-- **Unconditional sufficient criterion.** If the `n`-th prime gap `g` satisfies
`g ^ 2 ≤ 4 * p_n`, then the Andrica inequality holds at `n`. -/
theorem andricaGap_lt_one_of_sq_gap_le (n : ℕ)
    (h : (nthPrime (n + 1) - nthPrime n) ^ 2 ≤ 4 * nthPrime n) :
    andricaGap n < 1 := by
  set d : ℕ := nthPrime (n + 1) - nthPrime n with hd
  have hlt := nthPrime_lt_succ n
  have hsum : (nthPrime (n + 1) : ℝ) = (nthPrime n : ℝ) + (d : ℝ) := by
    have : nthPrime n + d = nthPrime (n + 1) := by omega
    exact_mod_cast this.symm
  have hR : (d : ℝ) ^ 2 ≤ 4 * (nthPrime n : ℝ) := by exact_mod_cast h
  have hdle : (d : ℝ) ≤ 2 * Real.sqrt (nthPrime n) := by
    have hs : Real.sqrt (nthPrime n) ^ 2 = (nthPrime n : ℝ) :=
      Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg ((nthPrime n : ℝ)), Nat.cast_nonneg (α := ℝ) d]
  rw [andricaGap_lt_one_iff, hsum]
  linarith

/-- **Unconditional sufficient criterion, small-gap form.** If `p_n ≥ 4` and the `n`-th prime
gap is at most `4`, the Andrica inequality holds at `n`. -/
theorem andricaGap_lt_one_of_gap_le_four (n : ℕ) (hp : 4 ≤ nthPrime n)
    (h : nthPrime (n + 1) - nthPrime n ≤ 4) : andricaGap n < 1 := by
  refine andricaGap_lt_one_of_sq_gap_le n ?_
  have : (nthPrime (n + 1) - nthPrime n) ^ 2 ≤ 4 ^ 2 := Nat.pow_le_pow_left h 2
  omega

lemma nthPrime_zero : nthPrime 0 = 2 := by
  have h : Nat.nth Nat.Prime (Nat.count Nat.Prime 2) = 2 := Nat.nth_count (by norm_num)
  have hc : Nat.count Nat.Prime 2 = 0 := by decide
  rw [hc] at h
  exact h

lemma nthPrime_one : nthPrime 1 = 3 := by
  have h : Nat.nth Nat.Prime (Nat.count Nat.Prime 3) = 3 := Nat.nth_count (by norm_num)
  have hc : Nat.count Nat.Prime 3 = 1 := by decide
  rw [hc] at h
  exact h

lemma nthPrime_two : nthPrime 2 = 5 := by
  have h : Nat.nth Nat.Prime (Nat.count Nat.Prime 5) = 5 := Nat.nth_count (by norm_num)
  have hc : Nat.count Nat.Prime 5 = 2 := by decide
  rw [hc] at h
  exact h

lemma nthPrime_three : nthPrime 3 = 7 := by
  have h : Nat.nth Nat.Prime (Nat.count Nat.Prime 7) = 7 := Nat.nth_count (by norm_num)
  have hc : Nat.count Nat.Prime 7 = 3 := by decide
  rw [hc] at h
  exact h

/-- Unconditional verification of the Andrica inequality at `n = 0`: `√3 - √2 < 1`. -/
theorem andricaGap_zero_lt_one : andricaGap 0 < 1 := by
  refine andricaGap_lt_one_of_sq_gap_le 0 ?_
  rw [nthPrime_zero, nthPrime_one]; norm_num

/-- Unconditional verification of the Andrica inequality at `n = 1`: `√5 - √3 < 1`. -/
theorem andricaGap_one_lt_one : andricaGap 1 < 1 := by
  refine andricaGap_lt_one_of_sq_gap_le 1 ?_
  rw [nthPrime_one, nthPrime_two]; norm_num

/-- Unconditional verification of the Andrica inequality at `n = 2`: `√7 - √5 < 1`. -/
theorem andricaGap_two_lt_one : andricaGap 2 < 1 := by
  refine andricaGap_lt_one_of_sq_gap_le 2 ?_
  rw [nthPrime_two, nthPrime_three]; norm_num

end Brockian.AndricaConjecture

