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
/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists

(The header block above is repeated here as a module docstring: Lean requires `import`
commands to precede any doc comment, so the file-opening header is an ordinary comment.)

Unitary divisors, the unitary divisor sum `σ*`, unitary perfect numbers, verification of the
five known unitary perfect numbers, the fact that no odd number `> 1` is unitary perfect, and
a reduction of the open "sixth unitary perfect number" problem.
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d ∣ n` with `gcd (d, n / d) = 1`. -/

theorem three_le_card_primeFactors_of_unitaryPerfect {n : ℕ} (h : IsUnitaryPerfect n)
    (hn6 : n ≠ 6) : 3 ≤ n.primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have hn0 : n ≠ 0 := h.1.ne'
  have hn1 : 1 < n := by
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · omega
      · have h1 := h.2
        rw [sigmaStar_one] at h1
        omega
    · omega
  set a := n.factorization 2 with hadef
  set m := n / 2 ^ a with hmdef
  have hsplit : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have ha : 1 ≤ a :=
    Nat.prime_two.factorization_pos_of_dvd hn0 (even_of_unitaryPerfect h hn1).two_dvd
  have hm0 : 0 < m := Nat.ordCompl_pos 2 hn0
  have hmodd : Odd m := by
    have h2 : ¬ (2 ∣ m) := Nat.not_dvd_ordCompl Nat.prime_two hn0
    exact Nat.odd_iff.2 (by omega)
  have hA2 : 2 ≤ 2 ^ a := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hcard : n.primeFactors.card = 1 + m.primeFactors.card := by
    conv_lhs => rw [← hsplit]
    exact card_primeFactors_two_pow_mul ha hmodd hm0
  have hmcard : m.primeFactors.card ≤ 1 := by omega
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 hm0.ne') with hm1 | hm1
  · -- `m = 1`, i.e. `n = 2 ^ a`, which is never unitary perfect
    have hnp : n = 2 ^ a := by rw [← hsplit, ← hm1, mul_one]
    have h2 := h.2
    rw [hnp, sigmaStar_prime_pow Nat.prime_two (by omega)] at h2
    omega
  · -- `m > 1` has exactly one prime factor, so `n = 2 ^ a * q ^ j` and hence `n = 6`
    have hpos : 0 < m.primeFactors.card :=
      Finset.card_pos.2 (Nat.nonempty_primeFactors.2 hm1)
    have hpp : IsPrimePow m := isPrimePow_iff_card_primeFactors_eq_one.2 (by omega)
    obtain ⟨q, j, hq, hj, hqm⟩ := hpp
    have hq' : q.Prime := Nat.prime_iff.2 hq
    have hqodd : Odd q := hmodd.of_dvd_nat (hqm ▸ dvd_pow_self q hj.ne')
    have hup : IsUnitaryPerfect (2 ^ a * q ^ j) := by rw [hqm, hsplit]; exact h
    have := eq_six_of_unitaryPerfect_two_pow_mul_prime_pow ha hq' hqodd hj hup
    rw [hqm, hsplit] at this
    exact hn6 this

/-! ## Reduction of the sixth-unitary-perfect problem -/

/-- **Reduction theorem.** A sixth unitary perfect number exists if and only if there are
`a ≥ 1` and an odd `m ≥ 1` with `(2 ^ a + 1) σ*(m) = 2 ^ (a+1) m` such that `2 ^ a * m` is
not one of the five known unitary perfect numbers. -/
