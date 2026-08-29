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

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: divisors `d` with `gcd (d, n / d) = 1`. -/

theorem eq_six_of_card_primeFactors_eq_two {n : ℕ} (h : IsUnitaryPerfect n)
    (hcard : n.primeFactors.card = 2) : n = 6 := by
  obtain ⟨hpos, heq⟩ := h
  have hn0 : n ≠ 0 := hpos.ne'
  have h2 : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two,
      (even_iff_two_dvd.mp (even_of_isUnitaryPerfect ⟨hpos, heq⟩)), hn0⟩
  obtain ⟨p, hset, hp2⟩ : ∃ p, n.primeFactors = {2, p} ∧ p ≠ 2 := by
    obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.mp hcard
    rw [hs] at h2
    rcases Finset.mem_insert.mp h2 with rfl | hy
    · exact ⟨y, hs, fun h => hxy h.symm⟩
    · rw [Finset.mem_singleton] at hy
      subst hy
      exact ⟨x, by rw [hs, Finset.pair_comm], hxy⟩
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hset]; simp)
  have hpmem : p ∈ n.primeFactors := by rw [hset]; simp
  set a := n.factorization 2 with ha
  set b := n.factorization p with hb
  have hne : (2 : ℕ) ≠ p := fun h => hp2 h.symm
  have hn : n = 2 ^ a * p ^ b := by
    conv_lhs => rw [← prod_primeFactors_pow_factorization hn0]
    rw [hset, Finset.prod_pair hne]
  have hus : usigma n = (2 ^ a + 1) * (p ^ b + 1) := by
    rw [usigma_eq_prod hn0, hset, Finset.prod_pair hne]
  have ha1 : a ≠ 0 := factorization_ne_zero_of_mem_primeFactors h2
  have hb1 : b ≠ 0 := factorization_ne_zero_of_mem_primeFactors hpmem
  have hA : 2 ≤ 2 ^ a := by
    calc (2 : ℕ) = 2 ^ 1 := rfl
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp3 : 3 ≤ p := by have := hpp.two_le; omega
  have hB : 3 ≤ p ^ b := by
    calc (3 : ℕ) ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ b := Nat.pow_le_pow_right (by omega) (by omega)
  rw [hus, hn] at heq
  set A := 2 ^ a with hAdef
  set B := p ^ b with hBdef
  have key : (A - 1) * (B - 1) = 2 := by
    have h1 : A + 1 = (A - 1) + 2 := by omega
    have h2' : B + 1 = (B - 1) + 2 := by omega
    have h3 : A = (A - 1) + 1 := by omega
    have h4 : B = (B - 1) + 1 := by omega
    rw [h1, h2'] at heq
    nlinarith [heq, h3, h4]
  have hle : A - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) ⟨B - 1, key.symm⟩
  have h2A : 2 ∣ A := dvd_pow_self 2 ha1
  have hAeq : A = 2 := by
    rcases (show A - 1 = 1 ∨ A - 1 = 2 by
      rcases Nat.eq_zero_or_pos (A - 1) with h | h
      · rw [h] at key; simp at key
      · omega) with h | h
    · omega
    · exfalso
      have h3A : A = 3 := by omega
      rw [h3A] at h2A
      omega
  have hBeq : B = 3 := by
    rw [hAeq] at key
    omega
  rw [hn, hAeq, hBeq]

