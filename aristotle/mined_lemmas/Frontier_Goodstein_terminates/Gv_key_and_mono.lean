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


theorem Gv_key_and_mono (b : ℕ) (w : Ordinal) (hb : 2 ≤ b) (hw : (b : Ordinal) ≤ w) (n : ℕ) :
    (∀ k : ℕ, n < b ^ k → Gv b w n < w ^ (Gv b w k)) ∧
      (∀ m : ℕ, n < m → Gv b w n < Gv b w m) := by
  have hb0 : 0 < b := by omega
  have hwpos : (0 : Ordinal) < w := lt_of_lt_of_le (by exact_mod_cast hb0) hw
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    have key : ∀ k : ℕ, n < b ^ k → Gv b w n < w ^ (Gv b w k) := by
      intro k hk
      rcases eq_or_ne n 0 with rfl | hn
      · simpa using opow_pos (Gv b w k) hwpos
      · have hLn : Nat.log b n < n := Nat.log_lt_self b hn
        have hrn : n % b ^ Nat.log b n < n := nat_mod_pow_log_lt b n hn
        have hrb : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ (nat_pow_log_pos b n)
        have hqb : n / b ^ Nat.log b n < b := nat_div_pow_log_lt b n hb
        have hLk : Nat.log b n < k := by
          have h1 : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
          exact (Nat.pow_lt_pow_iff_right hb).mp (lt_of_le_of_lt h1 hk)
        have hGLk : Gv b w (Nat.log b n) < Gv b w k := (IH _ hLn).2 k hLk
        have hGr : Gv b w (n % b ^ Nat.log b n) < w ^ (Gv b w (Nat.log b n)) :=
          (IH _ hrn).1 (Nat.log b n) hrb
        calc Gv b w n
            = w ^ (Gv b w (Nat.log b n)) * ((n / b ^ Nat.log b n : ℕ))
                + Gv b w (n % b ^ Nat.log b n) := Gv_def b w n hn
          _ < w ^ (Gv b w (Nat.log b n)) * ((n / b ^ Nat.log b n : ℕ))
                + w ^ (Gv b w (Nat.log b n)) := add_lt_add_right hGr _
          _ = w ^ (Gv b w (Nat.log b n)) * (((n / b ^ Nat.log b n : ℕ) : Ordinal) + 1) := by
                rw [mul_add, mul_one]
          _ ≤ w ^ (Gv b w (Nat.log b n)) * w := by
                apply mul_le_mul_right
                have h2 : ((n / b ^ Nat.log b n : ℕ) + 1 : ℕ) ≤ b := hqb
                calc ((n / b ^ Nat.log b n : ℕ) : Ordinal) + 1
                    = (((n / b ^ Nat.log b n : ℕ) + 1 : ℕ) : Ordinal) := by push_cast; rfl
                  _ ≤ (b : Ordinal) := by exact_mod_cast h2
                  _ ≤ w := hw
          _ = w ^ (Gv b w (Nat.log b n) + 1) := by rw [opow_add, opow_one]
          _ ≤ w ^ (Gv b w k) := opow_le_opow_right hwpos (Order.add_one_le_of_lt hGLk)
    refine ⟨key, ?_⟩
    intro m hnm
    have hm : m ≠ 0 := by omega
    have hGm : Gv b w m = w ^ (Gv b w (Nat.log b m)) * ((m / b ^ Nat.log b m : ℕ))
        + Gv b w (m % b ^ Nat.log b m) := Gv_def b w m hm
    have hqm0 : 0 < m / b ^ Nat.log b m := nat_div_pow_log_pos b m hm
    have hbase : w ^ (Gv b w (Nat.log b m)) ≤ Gv b w m := by
      rw [hGm]
      calc w ^ (Gv b w (Nat.log b m)) = w ^ (Gv b w (Nat.log b m)) * 1 := (mul_one _).symm
        _ ≤ w ^ (Gv b w (Nat.log b m)) * ((m / b ^ Nat.log b m : ℕ)) := by
              apply mul_le_mul_right
              exact_mod_cast hqm0
        _ ≤ _ := le_self_add
    rcases eq_or_ne n 0 with rfl | hn
    · simpa using Gv_pos b w hwpos m hm
    · have hLM : Nat.log b n ≤ Nat.log b m := Nat.log_mono_right (le_of_lt hnm)
      rcases lt_or_eq_of_le hLM with hlt | heq
      · have hnlt : n < b ^ Nat.log b m :=
          lt_of_lt_of_le (Nat.lt_pow_succ_log_self hb n) (Nat.pow_le_pow_right hb0 hlt)
        exact lt_of_lt_of_le (key _ hnlt) hbase
      · have hrn : n % b ^ Nat.log b n < n := nat_mod_pow_log_lt b n hn
        have hrb : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ (nat_pow_log_pos b n)
        have hGr : Gv b w (n % b ^ Nat.log b n) < w ^ (Gv b w (Nat.log b n)) :=
          (IH _ hrn).1 (Nat.log b n) hrb
        have hGn : Gv b w n = w ^ (Gv b w (Nat.log b n)) * ((n / b ^ Nat.log b n : ℕ))
            + Gv b w (n % b ^ Nat.log b n) := Gv_def b w n hn
        have hdn := Nat.div_add_mod n (b ^ Nat.log b n)
        rw [heq] at hrn hrb hGr hGn hdn
        have hdm := Nat.div_add_mod m (b ^ Nat.log b m)
        have hqle : n / b ^ Nat.log b m ≤ m / b ^ Nat.log b m :=
          Nat.div_le_div_right (le_of_lt hnm)
        rcases lt_or_eq_of_le hqle with hq | hq
        · calc Gv b w n
              = w ^ (Gv b w (Nat.log b m)) * ((n / b ^ Nat.log b m : ℕ))
                  + Gv b w (n % b ^ Nat.log b m) := hGn
            _ < w ^ (Gv b w (Nat.log b m)) * ((n / b ^ Nat.log b m : ℕ))
                  + w ^ (Gv b w (Nat.log b m)) := add_lt_add_right hGr _
            _ = w ^ (Gv b w (Nat.log b m)) * (((n / b ^ Nat.log b m : ℕ) : Ordinal) + 1) := by
                  rw [mul_add, mul_one]
            _ ≤ w ^ (Gv b w (Nat.log b m)) * ((m / b ^ Nat.log b m : ℕ)) := by
                  apply mul_le_mul_right
                  have h3 : ((n / b ^ Nat.log b m : ℕ) + 1 : ℕ) ≤ m / b ^ Nat.log b m := hq
                  calc ((n / b ^ Nat.log b m : ℕ) : Ordinal) + 1
                      = (((n / b ^ Nat.log b m : ℕ) + 1 : ℕ) : Ordinal) := by push_cast; rfl
                    _ ≤ _ := by exact_mod_cast h3
            _ ≤ Gv b w m := by rw [hGm]; exact le_self_add
        · have hrlt : n % b ^ Nat.log b m < m % b ^ Nat.log b m := by
            refine lt_of_add_lt_add_left (a := b ^ Nat.log b m * (m / b ^ Nat.log b m)) ?_
            rw [hdm, ← hq, hdn]
            exact hnm
          have hGrr : Gv b w (n % b ^ Nat.log b m) < Gv b w (m % b ^ Nat.log b m) :=
            (IH _ hrn).2 _ hrlt
          calc Gv b w n
              = w ^ (Gv b w (Nat.log b m)) * ((n / b ^ Nat.log b m : ℕ))
                  + Gv b w (n % b ^ Nat.log b m) := hGn
            _ < w ^ (Gv b w (Nat.log b m)) * ((m / b ^ Nat.log b m : ℕ))
                  + Gv b w (m % b ^ Nat.log b m) := by
                  rw [hq]; exact add_lt_add_right hGrr _
            _ = Gv b w m := hGm.symm

