/-
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

/-! ## Elementary facts about base-`b` digits -/


theorem hval_key (h : HypSet α b pw mul) (hb : 2 ≤ b) (n : ℕ) :
    (∀ m, m < n → hval b pw mul m < hval b pw mul n) ∧
      (∀ m, m < b ^ n → hval b pw mul m < pw (hval b pw mul n)) := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    have part1 : ∀ m, m < n → hval b pw mul m < hval b pw mul n := by
      intro m hmn
      have hn : n ≠ 0 := by omega
      have hEn : Nat.log b n < n := Nat.log_lt_self b hn
      have hrb : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ (pow_log_pos b n)
      have hrn : n % b ^ Nat.log b n < n := mod_pow_log_lt hn
      have hc1 : 1 ≤ n / b ^ Nat.log b n := digit_pos hn
      have hvn : hval b pw mul n =
          mul (pw (hval b pw mul (Nat.log b n))) (n / b ^ Nat.log b n)
            + hval b pw mul (n % b ^ Nat.log b n) := hval_eq b pw mul hn
      set A := pw (hval b pw mul (Nat.log b n)) with hA
      have hQE : ∀ x, x < b ^ Nat.log b n → hval b pw mul x < A := (IH _ hEn).2
      have htail : ∀ x : α, x ≤ mul A (n / b ^ Nat.log b n) →
          x ≤ hval b pw mul n := by
        intro x hx
        refine hx.trans ?_
        rw [hvn]
        have := h.add_le_left (mul A (n / b ^ Nat.log b n)) 0
          (hval b pw mul (n % b ^ Nat.log b n)) (h.zero_le _)
        simpa [h.add_zero'] using this
      rcases eq_or_ne m 0 with rfl | hm0
      · simpa using hval_pos h hn
      · have hvm : hval b pw mul m =
            mul (pw (hval b pw mul (Nat.log b m))) (m / b ^ Nat.log b m)
              + hval b pw mul (m % b ^ Nat.log b m) := hval_eq b pw mul hm0
        have hEE' : Nat.log b m ≤ Nat.log b n := Nat.log_mono_right hmn.le
        rcases lt_or_eq_of_le hEE' with hlt | heq
        · have h1 : m < b ^ Nat.log b n :=
            lt_of_lt_of_le (Nat.lt_pow_succ_log_self hb m)
              (Nat.pow_le_pow_right (by omega) (by omega))
          refine lt_of_lt_of_le (hQE m h1) (htail A ?_)
          calc A = mul A 1 := (h.mul_one' A).symm
            _ ≤ mul A (n / b ^ Nat.log b n) := h.mul_mono _ _ _ hc1
        · rw [heq] at hvm
          have hdiv : m / b ^ Nat.log b n ≤ n / b ^ Nat.log b n :=
            Nat.div_le_div_right hmn.le
          have hr'b : m % b ^ Nat.log b n < b ^ Nat.log b n := by
            rw [← heq]; exact Nat.mod_lt _ (pow_log_pos b m)
          rcases lt_or_eq_of_le hdiv with hcc | hcc
          · rw [hvm]
            have step1 : mul A (m / b ^ Nat.log b n) + hval b pw mul (m % b ^ Nat.log b n)
                < mul A (m / b ^ Nat.log b n) + A :=
              h.add_lt_left _ _ _ (hQE _ hr'b)
            refine lt_of_lt_of_le step1 (htail _ ?_)
            calc mul A (m / b ^ Nat.log b n) + A
                = mul A (m / b ^ Nat.log b n + 1) := (h.mul_succ' _ _).symm
              _ ≤ mul A (n / b ^ Nat.log b n) := h.mul_mono _ _ _ hcc
          · -- same leading digit: compare the remainders
            have hmm : b ^ Nat.log b n * (m / b ^ Nat.log b n) + m % b ^ Nat.log b n = m :=
              Nat.div_add_mod m _
            have hnn : b ^ Nat.log b n * (n / b ^ Nat.log b n) + n % b ^ Nat.log b n = n :=
              Nat.div_add_mod n _
            have hrr : m % b ^ Nat.log b n < n % b ^ Nat.log b n := by
              rw [hcc] at hmm; omega
            rw [hvm, hvn, hcc]
            exact h.add_lt_left _ _ _ ((IH _ hrn).1 _ hrr)
    refine ⟨part1, ?_⟩
    intro m hm
    rcases eq_or_ne m 0 with rfl | hm0
    · simpa using h.pw_pos (hval b pw mul n)
    · have hE'n : Nat.log b m < n := Nat.log_lt_of_lt_pow hm0 hm
      have hr' : m % b ^ Nat.log b m < b ^ Nat.log b m := Nat.mod_lt _ (pow_log_pos b m)
      have hc'b : m / b ^ Nat.log b m < b := digit_lt hb
      have hQE' := (IH _ hE'n).2
      have hlt : hval b pw mul (Nat.log b m) < hval b pw mul n := part1 _ hE'n
      calc hval b pw mul m
          = mul (pw (hval b pw mul (Nat.log b m))) (m / b ^ Nat.log b m)
              + hval b pw mul (m % b ^ Nat.log b m) := hval_eq b pw mul hm0
        _ < mul (pw (hval b pw mul (Nat.log b m))) (m / b ^ Nat.log b m)
              + pw (hval b pw mul (Nat.log b m)) := h.add_lt_left _ _ _ (hQE' _ hr')
        _ = mul (pw (hval b pw mul (Nat.log b m))) (m / b ^ Nat.log b m + 1) :=
              (h.mul_succ' _ _).symm
        _ ≤ pw (hval b pw mul (Nat.log b m) + 1) := h.pw_step _ _ (by omega)
        _ ≤ pw (hval b pw mul n) := h.pw_mono _ _ (h.add_one_le _ _ hlt)

