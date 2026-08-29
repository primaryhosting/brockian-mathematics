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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` commands to precede every other command, including
module doc comments, so the header above is a plain comment and is repeated as the
module docstring after the import below.)
-/

import Mathlib

/-!
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if the sum of all its divisors equals `2 * n + 1`,
i.e. `σ n = 2n + 1`.  Whether a quasiperfect number exists is an open problem. -/

theorem quasiperfect_eq_odd_sq {n : ℕ} (h : Quasiperfect n) :
    ∃ k, Odd k ∧ 1 < k ∧ n = k ^ 2 := by
  obtain ⟨hn0, hs⟩ := h
  -- first: `n` is odd
  have hodd : Odd n := by
    obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn0.ne'
    by_contra hcon
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | hpos
      · exact absurd (by simpa using hm) hcon
      · exact hpos
    have hm0 : m ≠ 0 := by rintro rfl; simp at hn0
    have hcop : (2 ^ a).Coprime m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
    have hsplit : ∑ d ∈ (2 ^ a * m).divisors, d
        = (∑ d ∈ (2 ^ a).divisors, d) * ∑ d ∈ m.divisors, d := Nat.Coprime.sum_divisors_mul hcop
    set D := ∑ d ∈ (2 ^ a).divisors, d with hDdef
    set S := ∑ d ∈ m.divisors, d with hSdef
    have hDS : D * S = 2 * (2 ^ a * m) + 1 := by rw [← hsplit]; exact hs
    have hD1 : D + 1 = 2 ^ (a + 1) := sum_divisors_two_pow a
    -- `S` is odd, hence `m` is a square
    have hSodd : Odd S := by
      rcases Nat.even_or_odd S with he | ho
      · exfalso
        obtain ⟨t, ht⟩ := he
        have : Even (D * S) := ⟨D * t, by rw [ht]; ring⟩
        rw [hDS] at this
        rcases this with ⟨u, hu⟩
        omega
      · exact ho
    obtain ⟨k, hk⟩ := isSquare_of_odd_sigma hm0 hm hSodd
    -- derive `D ∣ k ^ 2 + 1`
    have hk2 : m = k ^ 2 := by rw [hk]; ring
    have hpow : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
    have hDS2 : D * S = D * k ^ 2 + (k ^ 2 + 1) := by
      have : 2 * (2 ^ a * m) = (D + 1) * k ^ 2 := by
        rw [hD1, hk2]; rw [hpow]; ring
      rw [hDS, this]; ring
    have hpow4 : 4 ≤ 2 ^ (a + 1) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hD0 : 0 < D := by omega
    have hkS : k ^ 2 ≤ S := Nat.le_of_mul_le_mul_left (by omega) hD0
    have hdvd : D ∣ k ^ 2 + 1 := by
      refine ⟨S - k ^ 2, ?_⟩
      rw [Nat.mul_sub]
      omega
    have hD4 : D % 4 = 3 := by
      obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      subst hb
      have : 2 ^ (b + 1 + 1) = 4 * 2 ^ b := by ring
      have h2b : 1 ≤ 2 ^ b := Nat.one_le_two_pow
      omega
    exact not_dvd_sq_add_one_of_three_mod_four hD4 hdvd
  -- now: `n` odd with odd `σ n` gives a square
  have hSodd : Odd (∑ d ∈ n.divisors, d) := by rw [hs]; exact ⟨n, by ring⟩
  obtain ⟨k, hk⟩ := isSquare_of_odd_sigma hn0.ne' hodd hSodd
  have hk2 : n = k ^ 2 := by rw [hk]; ring
  refine ⟨k, ?_, ?_, hk2⟩
  · rcases Nat.even_or_odd k with he | ho
    · exfalso
      rw [Nat.odd_iff] at hodd
      obtain ⟨t, ht⟩ := he
      rw [hk2, ht] at hodd
      have : (2 * t) ^ 2 % 2 = 0 := by
        have : (2 * t) ^ 2 = 2 * (2 * t * t) := by ring
        omega
      rw [show t + t = 2 * t by ring] at hodd
      omega
    · exact ho
  · by_contra hcon
    have hk1 : k = 1 ∨ k = 0 := by omega
    rcases hk1 with rfl | rfl
    · rw [hk2] at hs; norm_num at hs
    · rw [hk2] at hn0; norm_num at hn0

/-- A quasiperfect number is odd. -/
