/-
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- written as a plain block comment; it is repeated as a module docstring below.)

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

/-! ## Hereditary base representations

For a base `b ≥ 2`, every positive natural number `n` can be written as
`n = b ^ e * c + r` with `e = Nat.log b n`, `1 ≤ c < b` and `r < b ^ e`, and iterating this
inside the exponent yields the *hereditary base-`b` representation* of `n`.

Two operations are defined by this recursion:

* `ordOf b n` : the ordinal obtained by replacing the base `b` by `ω` in the hereditary
  base-`b` representation of `n` (a "Goodstein ordinal", an ordinal `< ε₀`);
* `shiftBase b n` : the natural number obtained by replacing the base `b` by `b + 1`
  in the hereditary base-`b` representation of `n`.
-/


lemma ordOf_key {b : ℕ} (hb : 2 ≤ b) (N : ℕ) :
    (∀ m, m < N → ordOf b m < ordOf b N) ∧ (∀ x, x < b ^ N → ordOf b x < ω ^ ordOf b N) := by
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  have part1 : ∀ m, m < N → ordOf b m < ordOf b N := by
    intro m hm
    have hN : N ≠ 0 := by omega
    have hNeq : ordOf b N =
        ω ^ ordOf b (Nat.log b N) * ((N / b ^ Nat.log b N : ℕ) : Ordinal)
          + ordOf b (N % b ^ Nat.log b N) := ordOf_eq_of_ne_zero hN
    have heN : Nat.log b N < N := Nat.log_lt_self b hN
    have hrlt : N % b ^ Nat.log b N < b ^ Nat.log b N := Nat.mod_lt _ (pow_log_pos b N)
    have hcpos : 0 < N / b ^ Nat.log b N := div_pow_log_pos hN
    have hpos : (0 : Ordinal) <
        ω ^ ordOf b (Nat.log b N) * ((N / b ^ Nat.log b N : ℕ) : Ordinal) := by
      refine mul_pos (Ordinal.opow_pos _ Ordinal.omega0_pos) ?_
      exact_mod_cast hcpos
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · rw [ordOf_zero, hNeq]
      exact lt_of_lt_of_le hpos (le_self_add)
    · have hm0 : m ≠ 0 := by omega
      have hmeq : ordOf b m =
          ω ^ ordOf b (Nat.log b m) * ((m / b ^ Nat.log b m : ℕ) : Ordinal)
            + ordOf b (m % b ^ Nat.log b m) := ordOf_eq_of_ne_zero hm0
      have hr'lt : m % b ^ Nat.log b m < b ^ Nat.log b m := Nat.mod_lt _ (pow_log_pos b m)
      have hee : Nat.log b m ≤ Nat.log b N := Nat.log_mono_right (le_of_lt hm)
      rcases lt_or_eq_of_le hee with hlt | heq
      · have h1 : ordOf b (Nat.log b m) < ordOf b (Nat.log b N) := (IH _ heN).1 _ hlt
        have h2 : ordOf b (m % b ^ Nat.log b m) < ω ^ ordOf b (Nat.log b m) :=
          (IH _ (lt_trans hlt heN)).2 _ hr'lt
        have h3 : ordOf b m < ω ^ ordOf b (Nat.log b N) := by
          rw [hmeq]; exact opow_mul_add_lt_opow h1 h2
        refine lt_of_lt_of_le h3 ?_
        rw [hNeq]
        refine le_trans ?_ (le_self_add)
        calc ω ^ ordOf b (Nat.log b N) = ω ^ ordOf b (Nat.log b N) * 1 := by rw [mul_one]
          _ ≤ ω ^ ordOf b (Nat.log b N) * ((N / b ^ Nat.log b N : ℕ) : Ordinal) := by
              refine mul_le_mul_right ?_ _
              exact_mod_cast hcpos
      · rw [heq] at hmeq hr'lt
        have h2 : ordOf b (m % b ^ Nat.log b N) < ω ^ ordOf b (Nat.log b N) :=
          (IH _ heN).2 _ hr'lt
        have hcle : m / b ^ Nat.log b N ≤ N / b ^ Nat.log b N :=
          Nat.div_le_div_right (le_of_lt hm)
        rcases lt_or_eq_of_le hcle with hclt | hceq
        · rw [hNeq, hmeq]
          exact lt_of_lt_of_le (opow_mul_add_lt_opow_mul hclt h2) le_self_add
        · have hmd : b ^ Nat.log b N * (m / b ^ Nat.log b N) + m % b ^ Nat.log b N = m :=
            Nat.div_add_mod m (b ^ Nat.log b N)
          have hNd : b ^ Nat.log b N * (N / b ^ Nat.log b N) + N % b ^ Nat.log b N = N :=
            Nat.div_add_mod N (b ^ Nat.log b N)
          have hrr : m % b ^ Nat.log b N < N % b ^ Nat.log b N := by
            rw [hceq] at hmd
            omega
          have h3 : ordOf b (m % b ^ Nat.log b N) < ordOf b (N % b ^ Nat.log b N) :=
            (IH _ (lt_of_lt_of_le hrlt (Nat.pow_log_le_self b hN))).1 _ hrr
          rw [hmeq, hNeq, hceq]
          exact add_lt_add_right h3 _
  refine ⟨part1, ?_⟩
  intro x hx
  rcases Nat.eq_zero_or_pos x with rfl | hxpos
  · simpa using Ordinal.opow_pos (ordOf b N) Ordinal.omega0_pos
  · have hx0 : x ≠ 0 := by omega
    have hbe : b ^ Nat.log b x ≤ x := Nat.pow_log_le_self b hx0
    have heN : Nat.log b x < N := by
      by_contra hcon
      push_neg at hcon
      have : b ^ N ≤ b ^ Nat.log b x := Nat.pow_le_pow_right (by omega) hcon
      omega
    have h1 : ordOf b (Nat.log b x) < ordOf b N := part1 _ heN
    have h2 : ordOf b (x % b ^ Nat.log b x) < ω ^ ordOf b (Nat.log b x) :=
      (IH _ heN).2 _ (Nat.mod_lt _ (pow_log_pos b x))
    rw [ordOf_eq_of_ne_zero hx0]
    exact opow_mul_add_lt_opow h1 h2

