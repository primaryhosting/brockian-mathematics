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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.UnitaryPerfect

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd (d, n / d) = 1`. -/

theorem one_add_two_pow_dvd_oddPart {n : ℕ} (hn : IsUnitaryPerfect n) :
    (1 + 2 ^ n.factorization 2) ∣ n / 2 ^ n.factorization 2 := by
  obtain ⟨hpos, hper⟩ := hn
  have hn0 : n ≠ 0 := hpos.ne'
  have heven : Even n := even_of_isUnitaryPerfect ⟨hpos, hper⟩
  set a := n.factorization 2 with ha
  set m := n / 2 ^ a with hm
  have hsplit : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left _ (Nat.coprime_ordCompl Nat.prime_two hn0)
  have hapos : a ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn0 heven.two_dvd).ne'
  have hsig : (1 + 2 ^ a) * sigmaStar m = 2 * n := by
    rw [← sigmaStar_prime_pow Nat.prime_two hapos, ← sigmaStar_mul_of_coprime hcop, hsplit, hper]
  have hdvd : (1 + 2 ^ a) ∣ 2 ^ (a + 1) * m := by
    refine ⟨sigmaStar m, ?_⟩
    calc 2 ^ (a + 1) * m = 2 * (2 ^ a * m) := by ring
      _ = 2 * n := by rw [hsplit]
      _ = (1 + 2 ^ a) * sigmaStar m := hsig.symm
  have hodd : Odd (1 + 2 ^ a) := by
    have : Even (2 ^ a) := (Nat.even_pow' hapos).2 even_two
    obtain ⟨t, ht⟩ := this
    exact ⟨t, by omega⟩
  have hcop2 : Nat.Coprime (1 + 2 ^ a) (2 ^ (a + 1)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  exact hcop2.dvd_of_dvd_mul_left hdvd

/-! ### The main (conditional) statement -/

/-- **A sixth unitary perfect number.**  Whether a unitary perfect number other than the five
known ones (`6`, `60`, `90`, `87360`, `146361946186458562560000`) exists is an open problem, so
what is proved here is a conditional reduction: a sixth unitary perfect number exists if and
only if there is a unitary perfect number outside the known list, and any such number is
necessarily even, has at least two distinct prime factors, and its odd part is divisible by
`1 + 2 ^ a`, where `2 ^ a` is the exact power of `2` dividing it. -/
