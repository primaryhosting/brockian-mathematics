import Mathlib

/-!
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Ordinal

/-! ### Elementary facts about base-`b` digits -/


theorem hbEval_key {b : ℕ} (hb : 2 ≤ b) : ∀ N : ℕ,
    (∀ n ≤ N, ∀ m < n, hbEval b m < hbEval b n) ∧
      (∀ k ≤ N, ∀ n < b ^ k, hbEval b n < Ordinal.omega0 ^ hbEval b k) := by
  intro N
  induction N with
  | zero =>
    constructor
    · intro n hn m hm
      exact absurd hm (by omega)
    · intro k hk n hn
      have hk0 : k = 0 := by omega
      subst hk0
      have hn0 : n = 0 := by simpa using hn
      subst hn0
      simp
  | succ N ih =>
    obtain ⟨M, P⟩ := ih
    have M' : ∀ n ≤ N + 1, ∀ m < n, hbEval b m < hbEval b n := by
      intro n hn m hm
      rcases Nat.lt_or_ge n (N + 1) with h | h
      · exact M n (by omega) m hm
      · have hnN : n = N + 1 := by omega
        have hn0 : n ≠ 0 := by omega
        have hen : Nat.log b n < n := Nat.log_lt_self b hn0
        have hrn : n % b ^ Nat.log b n < n := mod_pow_log_lt_self b hn0
        have hd0 : 0 < n / b ^ Nat.log b n := leading_digit_pos b hn0
        have hnn := hbEval_eq b hn0
        have hlow : omega0 ^ hbEval b (Nat.log b n) * ((n / b ^ Nat.log b n : ℕ) : Ordinal)
            ≤ hbEval b n := by rw [hnn]; exact le_self_add
        rcases eq_or_ne m 0 with rfl | hm0
        · rw [hbEval_zero]
          refine lt_of_lt_of_le ?_ hlow
          exact mul_pos (opow_pos _ omega0_pos) (by exact_mod_cast hd0)
        · have hmm := hbEval_eq b hm0
          have hlog : Nat.log b m ≤ Nat.log b n := Nat.log_mono_right hm.le
          rcases lt_or_eq_of_le hlog with hlt | heq
          · have h1 : hbEval b m < omega0 ^ hbEval b (Nat.log b m + 1) :=
              P (Nat.log b m + 1) (by omega) m (Nat.lt_pow_succ_log_self (by omega) m)
            have h2 : hbEval b (Nat.log b m + 1) ≤ hbEval b (Nat.log b n) := by
              rcases eq_or_lt_of_le (show Nat.log b m + 1 ≤ Nat.log b n by omega) with heq' | hlt'
              · rw [heq']
              · exact le_of_lt (M (Nat.log b n) (by omega) _ hlt')
            have h3 : omega0 ^ hbEval b (Nat.log b m + 1) ≤ omega0 ^ hbEval b (Nat.log b n) :=
              opow_le_opow_right omega0_pos h2
            have h4 : omega0 ^ hbEval b (Nat.log b n)
                ≤ omega0 ^ hbEval b (Nat.log b n) * ((n / b ^ Nat.log b n : ℕ) : Ordinal) := by
              nth_rewrite 1 [show omega0 ^ hbEval b (Nat.log b n)
                  = omega0 ^ hbEval b (Nat.log b n) * 1 by simp]
              exact omega_mul_le (by exact_mod_cast hd0)
            exact lt_of_lt_of_le h1 (h3.trans (h4.trans hlow))
          · have hdle : m / b ^ Nat.log b n ≤ n / b ^ Nat.log b n := Nat.div_le_div_right hm.le
            rcases lt_or_eq_of_le hdle with hdlt | hdeq
            · have hr' : hbEval b (m % b ^ Nat.log b m) < omega0 ^ hbEval b (Nat.log b m) :=
                P (Nat.log b m) (by omega) _ (mod_lt_pow_log b m)
              have step1 : hbEval b m
                  < omega0 ^ hbEval b (Nat.log b m) * (((m / b ^ Nat.log b m : ℕ) : Ordinal) + 1) := by
                rw [hmm]; exact omega_mul_add_lt hr'
              have step2 : omega0 ^ hbEval b (Nat.log b m)
                  * (((m / b ^ Nat.log b m : ℕ) : Ordinal) + 1)
                  ≤ omega0 ^ hbEval b (Nat.log b n) * ((n / b ^ Nat.log b n : ℕ) : Ordinal) := by
                rw [heq]
                refine omega_mul_le ?_
                have h6 : ((m / b ^ Nat.log b n : ℕ) : Ordinal) + 1
                    = (((m / b ^ Nat.log b n) + 1 : ℕ) : Ordinal) := by push_cast; rfl
                rw [h6]
                exact_mod_cast Nat.succ_le_of_lt hdlt
              exact lt_of_lt_of_le step1 (step2.trans hlow)
            · have hrr : m % b ^ Nat.log b m < n % b ^ Nat.log b n := by
                have e1 := Nat.div_add_mod m (b ^ Nat.log b m)
                have e2 := Nat.div_add_mod n (b ^ Nat.log b n)
                rw [heq] at e1 ⊢
                rw [← hdeq] at e2
                omega
              have h5 := M (n % b ^ Nat.log b n) (by omega) _ hrr
              rw [heq] at h5
              rw [hmm, hnn, heq, hdeq]
              exact (add_lt_add_iff_left _).2 h5
    refine ⟨M', ?_⟩
    intro k hk n hn
    rcases Nat.lt_or_ge k (N + 1) with h | h
    · exact P k (by omega) n hn
    · have hkN : k = N + 1 := by omega
      rcases eq_or_ne n 0 with rfl | hn0
      · simpa using opow_pos (hbEval b k) omega0_pos
      · have hlogk : Nat.log b n < k := Nat.log_lt_of_lt_pow hn0 hn
        have hr' : hbEval b (n % b ^ Nat.log b n) < omega0 ^ hbEval b (Nat.log b n) :=
          P (Nat.log b n) (by omega) _ (mod_lt_pow_log b n)
        have hEe : hbEval b (Nat.log b n) < hbEval b k := M' k (by omega) _ hlogk
        calc hbEval b n
            < omega0 ^ hbEval b (Nat.log b n) * (((n / b ^ Nat.log b n : ℕ) : Ordinal) + 1) := by
              rw [hbEval_eq b hn0]; exact omega_mul_add_lt hr'
          _ ≤ omega0 ^ (hbEval b (Nat.log b n) + 1) := omega_mul_succ_le
          _ ≤ omega0 ^ hbEval b k :=
              opow_le_opow_right omega0_pos (Order.add_one_le_iff.mpr hEe)

