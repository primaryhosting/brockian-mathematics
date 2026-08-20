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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian
namespace SuperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

lemma not_superperfect_prime {p : ℕ} (hp : p.Prime) (hodd : Odd p) : ¬ Superperfect p := by
  intro hs
  obtain ⟨a, k, hk, hm, heq⟩ := odd_superperfect_structure hodd hs
  rw [sig_prime hp] at hm
  have ha : 1 ≤ a := by
    by_contra h
    interval_cases a
    · simp at hm
      obtain ⟨t, ht⟩ := hodd
      obtain ⟨s, hs'⟩ := hk
      omega
  set q := 2 ^ (a + 1) - 1 with hq
  have hqodd : Odd q := by
    have h1 : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
    obtain ⟨c, hc⟩ : 2 ∣ 2 ^ (a + 1) := dvd_pow_self 2 (by omega)
    exact ⟨c - 1, by omega⟩
  have hqdvd : q ∣ 2 * p := ⟨sig k, heq.symm⟩
  have hqp : q ∣ p := Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hqodd) hqdvd
  have hq3 : 3 ≤ q := by
    have : 2 ^ 2 ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hqeq : q = p := (hp.eq_one_or_self_of_dvd q hqp).resolve_left (by omega)
  rw [hqeq] at heq
  have hsk : p * sig k = p * 2 := by rw [heq]; ring
  exact sig_ne_two k (Nat.eq_of_mul_eq_mul_left hp.pos hsk)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Exhaustive search: no odd number below `1000` is superperfect. -/
