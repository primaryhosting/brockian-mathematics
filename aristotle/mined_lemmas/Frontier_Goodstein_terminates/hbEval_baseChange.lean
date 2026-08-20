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


theorem hbEval_baseChange {b c : ℕ} (hb : 2 ≤ b) (hbc : b ≤ c) (n : ℕ) :
    hbEval c (baseChange b c n) = hbEval b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hd0 : 0 < n / b ^ Nat.log b n := leading_digit_pos b hn0
      have hdb : n / b ^ Nat.log b n < b := leading_digit_lt hb n
      have hr : n % b ^ Nat.log b n < b ^ Nat.log b n := mod_lt_pow_log b n
      have hen : Nat.log b n < n := Nat.log_lt_self b hn0
      have hrn : n % b ^ Nat.log b n < n := mod_pow_log_lt_self b hn0
      have hR := baseChange_eq b c hn0
      have hRr : baseChange b c (n % b ^ Nat.log b n) < c ^ baseChange b c (Nat.log b n) :=
        baseChange_lt_pow hb hbc hr
      have hlogc : Nat.log c (baseChange b c n) = baseChange b c (Nat.log b n) := by
        rw [hR]; exact log_of_digits hd0 (by omega) hRr
      have hdivc : baseChange b c n / c ^ baseChange b c (Nat.log b n) = n / b ^ Nat.log b n := by
        rw [hR]; exact div_of_digits hRr
      have hmodc : baseChange b c n % c ^ baseChange b c (Nat.log b n)
          = baseChange b c (n % b ^ Nat.log b n) := by
        rw [hR]; exact mod_of_digits hRr
      have hBn0 : baseChange b c n ≠ 0 := (baseChange_pos hb hbc hn0).ne'
      rw [hbEval_eq c hBn0, hbEval_eq b hn0, hlogc, hdivc, hmodc, ih _ hen, ih _ hrn]

/-! ### Goodstein sequences -/

/-- The Goodstein sequence starting at `n`: `goodstein n 0 = n`, and `goodstein n (k+1)` is
obtained from `goodstein n k` by rewriting it in hereditary base `k+2`, replacing the base
`k+2` by `k+3`, and subtracting one. -/
