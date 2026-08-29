import Mathlib
/-!
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

open Ordinal

/-! ### Arithmetic preliminaries -/


theorem Gv_bump (b c : ℕ) (w : Ordinal) (hb : 2 ≤ b) (hbc : b ≤ c)
    (n : ℕ) : Gv c w (bump b c n) = Gv b w n := by
  have hc : 2 ≤ c := le_trans hb hbc
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hLn : Nat.log b n < n := Nat.log_lt_self b hn
      have hrn : n % b ^ Nat.log b n < n := nat_mod_pow_log_lt b n hn
      have hrb : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ (nat_pow_log_pos b n)
      have hq0 : 0 < n / b ^ Nat.log b n := nat_div_pow_log_pos b n hn
      have hqc : n / b ^ Nat.log b n < c := lt_of_lt_of_le (nat_div_pow_log_lt b n hb) hbc
      have hkey : bump b c (n % b ^ Nat.log b n) < c ^ bump b c (Nat.log b n) := by
        have h1 : Gv b (c : Ordinal) (n % b ^ Nat.log b n)
            < (c : Ordinal) ^ (Gv b (c : Ordinal) (Nat.log b n)) :=
          Gv_lt_opow b (c : Ordinal) hb (by exact_mod_cast hbc) _ _ hrb
        rw [← natCast_bump, ← natCast_bump, ← natCast_pow_ord] at h1
        exact_mod_cast h1
      have hx : bump b c n
          = c ^ (bump b c (Nat.log b n)) * (n / b ^ Nat.log b n)
            + bump b c (n % b ^ Nat.log b n) := bump_def b c n hn
      obtain ⟨h1, h2, h3⟩ := nat_decomp c (bump b c (Nat.log b n)) (n / b ^ Nat.log b n)
        (bump b c (n % b ^ Nat.log b n)) hc hq0 hqc hkey
      have hxne : bump b c n ≠ 0 := bump_ne_zero b c n (by omega) hn
      rw [Gv_def c w _ hxne, hx, h1, h2, h3, IH _ hLn, IH _ hrn, Gv_def b w n hn]

/-! ### The Goodstein sequence -/

/-- `goodstein n k` is the `k`-th term of the Goodstein sequence started at `n`
(with initial base `2`): at each step, write the current value in hereditary base `k + 2`,
replace the base by `k + 3`, and subtract one. -/
