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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.PracticalNumbers

/-!
## Overview

A positive integer `n` is *practical* if every `m ≤ n` is a sum of distinct divisors of `n`.
We prove that there are infinitely many `n` with `n` and `n + 2` both practical.

The construction: fix a large `a`, let `3 ^ b` be the largest power of `3` with `3 ^ b ≤ 2 ^ (a+1)`,
and let `s` be the representative in `[1, 3 ^ b)` of `-(2 ^ (a-1))⁻¹ mod 3 ^ b`.  Then

* `n = 2 ^ a * s` is practical because `s ≤ 3 ^ b ≤ 2 ^ (a+1) = σ(2 ^ a) + 1`;
* `n + 2 = 2 * (2 ^ (a-1) * s + 1)` where `3 ^ b` divides `2 ^ (a-1) * s + 1`, so writing
  `2 ^ (a-1) * s + 1 = 3 ^ b' * v` with `3 ∤ v` and `b' ≥ b`, we get `v ≤ 2 ^ (a-1) < 3 ^ (b'+1)`,
  which makes `2 * 3 ^ b' * v` practical.

Practicality of these two families is obtained from an explicit complete set of divisors
(`P2` for powers of two, `D3` for `2 * 3 ^ b`) together with a combination lemma
(`subsetSum_combine`), a constructive version of Stewart's criterion.
-/

/-- `SubsetSum D t` means `t` is the sum of a subset of the finite set `D`. -/

theorem exists_practical_twin_gt (N : ℕ) :
    ∃ n > N, Practical n ∧ Practical (n + 2) := by
  -- choose `a` large, and `b` maximal with `3 ^ b ≤ 2 ^ (a + 1)`
  set a := N + 3 with ha
  have ha2 : 2 ≤ a := by omega
  have hNa : N < 2 ^ a := lt_of_lt_of_le (by omega) (le_of_lt (Nat.lt_two_pow_self (n := a)))
  set b := Nat.log 3 (2 ^ (a + 1)) with hb
  have h2pos : (0 : ℕ) < 2 ^ (a + 1) := (by positivity)
  have h3le : (3 : ℕ) ^ 1 ≤ 2 ^ (a + 1) := by
    have : (2 : ℕ) ^ 3 ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at this ⊢
    omega
  have hb1 : 1 ≤ b := Nat.le_log_of_pow_le (by norm_num) h3le
  have hble : 3 ^ b ≤ 2 ^ (a + 1) := Nat.pow_log_le_self 3 h2pos.ne'
  have hblt : 2 ^ (a + 1) < 3 ^ (b + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hq1 : 1 < 3 ^ b := by
    calc (1 : ℕ) < 3 ^ 1 := by norm_num
      _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb1
  -- choose `s` with `2 ^ (a - 1) * s ≡ -1 mod 3 ^ b`
  have hcop : Nat.Coprime (2 ^ (a - 1)) (3 ^ b) := Nat.Coprime.pow _ _ (by decide)
  obtain ⟨mm, -, hmm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hq1
  set s := (mm * (3 ^ b - 1)) % 3 ^ b with hs
  have hs_lt : s < 3 ^ b := Nat.mod_lt _ (by omega)
  have hdvd : 3 ^ b ∣ 2 ^ (a - 1) * s + 1 := by
    have e1 : (2 ^ (a - 1) * mm) ≡ 1 [MOD 3 ^ b] := by
      unfold Nat.ModEq
      rw [hmm, Nat.mod_eq_of_lt hq1]
    have e2 : 2 ^ (a - 1) * s ≡ 2 ^ (a - 1) * (mm * (3 ^ b - 1)) [MOD 3 ^ b] :=
      Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)
    have e3 : 2 ^ (a - 1) * (mm * (3 ^ b - 1)) = (2 ^ (a - 1) * mm) * (3 ^ b - 1) := by ring
    have e4 : (2 ^ (a - 1) * mm) * (3 ^ b - 1) ≡ 1 * (3 ^ b - 1) [MOD 3 ^ b] :=
      Nat.ModEq.mul_right _ e1
    have e5 : 2 ^ (a - 1) * s + 1 ≡ 1 * (3 ^ b - 1) + 1 [MOD 3 ^ b] :=
      ((e2.trans (e3 ▸ e4))).add_right 1
    have e6 : 1 * (3 ^ b - 1) + 1 = 3 ^ b := by omega
    rw [e6] at e5
    exact (Nat.modEq_zero_iff_dvd).mp (e5.trans ((Nat.modEq_zero_iff_dvd).mpr dvd_rfl))
  have hs_pos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0, Nat.mul_zero] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    · exact h0
  refine ⟨2 ^ a * s, ?_, ?_, ?_⟩
  · calc N < 2 ^ a := hNa
      _ = 2 ^ a * 1 := by ring
      _ ≤ 2 ^ a * s := Nat.mul_le_mul_left _ hs_pos
  · exact practical_pow_two_mul s hs_pos a (by omega)
  · -- `n + 2 = 2 * u` with `u = 2 ^ (a - 1) * s + 1`
    set u := 2 ^ (a - 1) * s + 1 with hu
    have ha1 : a = (a - 1) + 1 := by omega
    have hpow : (2 : ℕ) ^ a = 2 * 2 ^ (a - 1) := by
      conv_lhs => rw [ha1]
      rw [pow_succ]
      ring
    have hn2 : 2 ^ a * s + 2 = 2 * u := by rw [hpow, hu]; ring
    have hu0 : u ≠ 0 := by positivity
    have hu_odd : ¬ 2 ∣ u := by
      have h2a : (2 : ℕ) ∣ 2 ^ (a - 1) * s :=
        Dvd.dvd.mul_right (dvd_pow_self 2 (by omega : a - 1 ≠ 0)) s
      obtain ⟨f, hf⟩ := h2a
      rw [hu]
      intro hcon
      obtain ⟨e, he⟩ := hcon
      omega
    -- extract the full power of `3`
    set b' := u.factorization 3 with hb'
    have hdvd' : (3 : ℕ) ^ b' ∣ u :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hu0).mpr le_rfl
    obtain ⟨v, huv'⟩ := hdvd'
    have huv : 3 ^ b' * v = u := huv'.symm
    have h3pos : (0 : ℕ) < 3 ^ b' := (by positivity)
    have hv0 : 0 < v := by
      rcases Nat.eq_zero_or_pos v with h0 | h0
      · rw [h0, Nat.mul_zero] at huv; exact absurd huv.symm hu0
      · exact h0
    have hv2 : ¬ 2 ∣ v := fun h => hu_odd (huv ▸ Dvd.dvd.mul_left h _)
    have hv3 : ¬ 3 ∣ v := by
      intro h
      obtain ⟨c, hc⟩ := h
      have hdd : (3 : ℕ) ^ (b' + 1) ∣ u := ⟨c, by rw [← huv, hc]; ring⟩
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hu0).mp hdd
      omega
    -- bound `v`
    have hbb' : b ≤ b' :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hu0).mp (hu ▸ hdvd)
    have hu_le : u ≤ 2 ^ (a - 1) * 3 ^ b := by
      have h1 : 1 ≤ (2 : ℕ) ^ (a - 1) := Nat.one_le_two_pow
      have h2 : 2 ^ (a - 1) * s ≤ 2 ^ (a - 1) * (3 ^ b - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have h3 : 2 ^ (a - 1) * (3 ^ b - 1) + 2 ^ (a - 1) = 2 ^ (a - 1) * 3 ^ b := by
        have : (3 : ℕ) ^ b - 1 + 1 = 3 ^ b := by omega
        calc 2 ^ (a - 1) * (3 ^ b - 1) + 2 ^ (a - 1)
            = 2 ^ (a - 1) * ((3 ^ b - 1) + 1) := by ring
          _ = 2 ^ (a - 1) * 3 ^ b := by rw [this]
      omega
    have hv_le : v ≤ 2 ^ (a - 1) := by
      have h1 : 3 ^ b' * v ≤ 2 ^ (a - 1) * 3 ^ b' := by
        calc 3 ^ b' * v = u := huv
          _ ≤ 2 ^ (a - 1) * 3 ^ b := hu_le
          _ ≤ 2 ^ (a - 1) * 3 ^ b' :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hbb')
      have h2 : 3 ^ b' * v ≤ 3 ^ b' * 2 ^ (a - 1) := by
        rw [Nat.mul_comm (3 ^ b') (2 ^ (a - 1))]
        exact h1
      exact Nat.le_of_mul_le_mul_left h2 h3pos
    have hv_le' : v ≤ 3 ^ (b' + 1) := by
      have h1 : (2 : ℕ) ^ (a - 1) ≤ 2 ^ (a + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (3 : ℕ) ^ (b + 1) ≤ 3 ^ (b' + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hfinal : 2 ^ a * s + 2 = 2 * 3 ^ b' * v := by
      rw [hn2, ← huv]; ring
    rw [hfinal]
    exact practical_two_pow_three_mul hv0 hv2 hv3 hv_le'

/-! ## Sanity checks on the definition -/

/-- A decidable reformulation of `Practical`, used for sanity checks. -/
