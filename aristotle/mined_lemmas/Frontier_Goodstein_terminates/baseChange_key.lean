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


theorem baseChange_key {b c : ℕ} (hb : 2 ≤ b) (hbc : b ≤ c) : ∀ N : ℕ,
    (∀ n ≤ N, ∀ m < n, baseChange b c m < baseChange b c n) ∧
      (∀ k ≤ N, ∀ n < b ^ k, baseChange b c n < c ^ baseChange b c k) := by
  have hc : 2 ≤ c := le_trans hb hbc
  intro N
  induction N with
  | zero =>
    refine ⟨fun n hn m hm => absurd hm (by omega), ?_⟩
    intro k hk n hn
    have hk0 : k = 0 := by omega
    subst hk0
    have hn0 : n = 0 := by simpa using hn
    subst hn0
    simp
  | succ N ih =>
    obtain ⟨M, P⟩ := ih
    have M' : ∀ n ≤ N + 1, ∀ m < n, baseChange b c m < baseChange b c n := by
      intro n hn m hm
      rcases Nat.lt_or_ge n (N + 1) with h | h
      · exact M n (by omega) m hm
      · have hn0 : n ≠ 0 := by omega
        have hen : Nat.log b n < n := Nat.log_lt_self b hn0
        have hrn : n % b ^ Nat.log b n < n := mod_pow_log_lt_self b hn0
        have hd0 : 0 < n / b ^ Nat.log b n := leading_digit_pos b hn0
        have hnn := baseChange_eq b c hn0
        have hcp : 0 < c ^ baseChange b c (Nat.log b n) := pow_pos (by omega) _
        have hlow : c ^ baseChange b c (Nat.log b n) * (n / b ^ Nat.log b n)
            ≤ baseChange b c n := by omega
        rcases eq_or_ne m 0 with rfl | hm0
        · have hpos : 0 < c ^ baseChange b c (Nat.log b n) * (n / b ^ Nat.log b n) :=
            Nat.mul_pos hcp hd0
          simp only [baseChange_zero]
          omega
        · have hmm := baseChange_eq b c hm0
          have hlog : Nat.log b m ≤ Nat.log b n := Nat.log_mono_right hm.le
          rcases lt_or_eq_of_le hlog with hlt | heq
          · have h1 : baseChange b c m < c ^ baseChange b c (Nat.log b m + 1) :=
              P (Nat.log b m + 1) (by omega) m (Nat.lt_pow_succ_log_self (by omega) m)
            have h2 : baseChange b c (Nat.log b m + 1) ≤ baseChange b c (Nat.log b n) := by
              rcases eq_or_lt_of_le (show Nat.log b m + 1 ≤ Nat.log b n by omega) with heq' | hlt'
              · rw [heq']
              · exact le_of_lt (M (Nat.log b n) (by omega) _ hlt')
            have h3 : c ^ baseChange b c (Nat.log b m + 1) ≤ c ^ baseChange b c (Nat.log b n) :=
              Nat.pow_le_pow_right (by omega) h2
            have h4 : c ^ baseChange b c (Nat.log b n)
                ≤ c ^ baseChange b c (Nat.log b n) * (n / b ^ Nat.log b n) :=
              Nat.le_mul_of_pos_right _ hd0
            omega
          · have hdle : m / b ^ Nat.log b n ≤ n / b ^ Nat.log b n := Nat.div_le_div_right hm.le
            rcases lt_or_eq_of_le hdle with hdlt | hdeq
            · have hr' : baseChange b c (m % b ^ Nat.log b m) < c ^ baseChange b c (Nat.log b m) :=
                P (Nat.log b m) (by omega) _ (mod_lt_pow_log b m)
              rw [heq] at hmm hr'
              have key : baseChange b c m
                  < c ^ baseChange b c (Nat.log b n) * (n / b ^ Nat.log b n) := by
                calc baseChange b c m
                    = c ^ baseChange b c (Nat.log b n) * (m / b ^ Nat.log b n)
                      + baseChange b c (m % b ^ Nat.log b n) := hmm
                  _ < c ^ baseChange b c (Nat.log b n) * (m / b ^ Nat.log b n)
                      + c ^ baseChange b c (Nat.log b n) := by omega
                  _ = c ^ baseChange b c (Nat.log b n) * (m / b ^ Nat.log b n + 1) := by ring
                  _ ≤ c ^ baseChange b c (Nat.log b n) * (n / b ^ Nat.log b n) :=
                      Nat.mul_le_mul_left _ (by omega)
              omega
            · have hrr : m % b ^ Nat.log b m < n % b ^ Nat.log b n := by
                have e1 := Nat.div_add_mod m (b ^ Nat.log b m)
                have e2 := Nat.div_add_mod n (b ^ Nat.log b n)
                rw [heq] at e1 ⊢
                rw [← hdeq] at e2
                omega
              have h5 := M (n % b ^ Nat.log b n) (by omega) _ hrr
              rw [heq] at hmm h5
              rw [hdeq] at hmm
              omega
    refine ⟨M', ?_⟩
    intro k hk n hn
    rcases Nat.lt_or_ge k (N + 1) with h | h
    · exact P k (by omega) n hn
    · rcases eq_or_ne n 0 with rfl | hn0
      · simpa using pow_pos (show 0 < c by omega) (baseChange b c k)
      · have hlogk : Nat.log b n < k := Nat.log_lt_of_lt_pow hn0 hn
        have hr' : baseChange b c (n % b ^ Nat.log b n) < c ^ baseChange b c (Nat.log b n) :=
          P (Nat.log b n) (by omega) _ (mod_lt_pow_log b n)
        have hEe : baseChange b c (Nat.log b n) < baseChange b c k := M' k (by omega) _ hlogk
        have hdb : n / b ^ Nat.log b n < b := leading_digit_lt hb n
        calc baseChange b c n
            = c ^ baseChange b c (Nat.log b n) * (n / b ^ Nat.log b n)
              + baseChange b c (n % b ^ Nat.log b n) := baseChange_eq b c hn0
          _ < c ^ baseChange b c (Nat.log b n) * (n / b ^ Nat.log b n)
              + c ^ baseChange b c (Nat.log b n) := by omega
          _ = c ^ baseChange b c (Nat.log b n) * (n / b ^ Nat.log b n + 1) := by ring
          _ ≤ c ^ baseChange b c (Nat.log b n) * c := Nat.mul_le_mul_left _ (by omega)
          _ = c ^ (baseChange b c (Nat.log b n) + 1) := by ring
          _ ≤ c ^ baseChange b c k := Nat.pow_le_pow_right (by omega) (by omega)

