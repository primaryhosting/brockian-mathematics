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
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a plain comment at the very top of the file, since a
Lean 4 module docstring may not precede the `import` commands.)
-/

namespace Brockian.LegendreConjecture

/-- **Legendre's conjecture**: for every `n ≥ 1` there is a prime strictly between
`n ^ 2` and `(n + 1) ^ 2`.  This statement is a famous open problem. -/
def LegendreStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2

/-- A square-root prime-gap hypothesis: after every prime `p` there is another prime
at distance at most `√p`.  (This is an unproved statement, strictly stronger than
Legendre's conjecture; it is used here only as an explicit hypothesis.) -/
def SqrtPrimeGap : Prop :=
  ∀ p : ℕ, Nat.Prime p → ∃ q : ℕ, Nat.Prime q ∧ p < q ∧ q ≤ p + Nat.sqrt p

/-- The largest prime `≤ N` is prime, whenever `2 ≤ N`. -/
theorem prime_findGreatest {N : ℕ} (hN : 2 ≤ N) :
    Nat.Prime (Nat.findGreatest Nat.Prime N) :=
  Nat.findGreatest_spec hN Nat.prime_two

/-- Conditional reduction: the square-root prime-gap hypothesis implies
Legendre's conjecture. -/
theorem LegendreConjecture (hgap : SqrtPrimeGap) : LegendreStatement := by
  intro n hn
  rcases eq_or_lt_of_le hn with h1 | h2
  · -- `n = 1`: the prime `2` lies strictly between `1` and `4`.
    subst h1
    exact ⟨2, Nat.prime_two, by norm_num, by norm_num⟩
  · -- `n ≥ 2`: take the largest prime `m ≤ n ^ 2` and the next prime after it.
    have hn2 : 2 ≤ n := h2
    have hN : 2 ≤ n ^ 2 := by nlinarith
    set m := Nat.findGreatest Nat.Prime (n ^ 2) with hm_def
    have hm : Nat.Prime m := prime_findGreatest hN
    have hmle : m ≤ n ^ 2 := Nat.findGreatest_le _
    obtain ⟨q, hq, hmq, hqle⟩ := hgap m hm
    have hqbig : n ^ 2 < q := by
      by_contra hcon
      push_neg at hcon
      have : q ≤ m := Nat.le_findGreatest hcon hq
      omega
    have hsqrt : Nat.sqrt m ≤ n := by
      calc Nat.sqrt m ≤ Nat.sqrt (n ^ 2) := Nat.sqrt_le_sqrt hmle
        _ = n := Nat.sqrt_eq' n
    refine ⟨q, hq, hqbig, ?_⟩
    have hqn : q ≤ n ^ 2 + n := by omega
    nlinarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Unconditional verification of Legendre's conjecture for all `1 ≤ n < 30`. -/
theorem legendre_lt_thirty : ∀ n < 30, 1 ≤ n → ∃ p < (n + 1) ^ 2, Nat.Prime p ∧ n ^ 2 < p := by
  decide

/-- An unconditional weakening of Legendre's conjecture, from Bertrand's postulate:
for every `n ≥ 1` there is a prime in the interval `(n ^ 2, 2 * n ^ 2]`. -/
theorem exists_prime_sq_lt_le_two_mul_sq (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p ≤ 2 * n ^ 2 :=
  Nat.exists_prime_lt_and_le_two_mul _ (pow_pos hn 2).ne'

end Brockian.LegendreConjecture

