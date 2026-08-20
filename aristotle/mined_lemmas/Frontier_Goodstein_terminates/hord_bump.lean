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


theorem hord_bump {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : hord (b + 1) (bump b n) = hord b n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hEn : Nat.log b n < n := Nat.log_lt_self b hn
      have hrn : n % b ^ Nat.log b n < n := mod_pow_log_lt hn
      have hrb : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ (pow_log_pos b n)
      have hc1 : 1 ≤ n / b ^ Nat.log b n := digit_pos hn
      have hcb : n / b ^ Nat.log b n < b := digit_lt hb
      set E := Nat.log b n with hEdef
      set c := n / b ^ E with hcdef
      set r := n % b ^ E with hrdef
      set P := bump b E with hPdef
      have hsmall : bump b r < (b + 1) ^ P := bump_lt_pow hb hrb
      have hM : bump b n = (b + 1) ^ P * c + bump b r := bump_eq b hn
      -- identify the leading exponent, digit and remainder of `bump b n` in base `b+1`
      have hpos : 0 < (b + 1) ^ P := pow_pos (Nat.succ_pos b) P
      have hle : (b + 1) ^ P ≤ bump b n := by
        rw [hM]; nlinarith [Nat.one_le_iff_ne_zero.mp hc1]
      have hlt : bump b n < (b + 1) ^ (P + 1) := by
        rw [hM, pow_succ]
        have : (b + 1) ^ P * c + bump b r < (b + 1) ^ P * c + (b + 1) ^ P := by omega
        calc (b + 1) ^ P * c + bump b r < (b + 1) ^ P * c + (b + 1) ^ P := this
          _ = (b + 1) ^ P * (c + 1) := by ring
          _ ≤ (b + 1) ^ P * (b + 1) := Nat.mul_le_mul_left _ (by omega)
      have hlog : Nat.log (b + 1) (bump b n) = P := Nat.log_eq_of_pow_le_of_lt_pow hle hlt
      have hdiv : bump b n / (b + 1) ^ P = c := by
        rw [hM, Nat.mul_add_div hpos, Nat.div_eq_of_lt hsmall, Nat.add_zero]
      have hmod : bump b n % (b + 1) ^ P = bump b r := by
        rw [hM, Nat.mul_add_mod, Nat.mod_eq_of_lt hsmall]
      have hMne : bump b n ≠ 0 := by
        have := hpos.trans_le hle; omega
      rw [hord_eq (b + 1) hMne, hlog, hdiv, hmod, IH E hEn, IH r hrn, hord_eq b hn]

/-! ## The Goodstein sequence -/

/-- `goodstein n k` is the `k`-th term of the Goodstein sequence starting at `n`;
the term `goodstein n k` is thought of as written in hereditary base `k + 2`. -/
