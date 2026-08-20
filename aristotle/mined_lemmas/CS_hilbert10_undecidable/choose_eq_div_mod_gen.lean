import RequestProject.DiophAux

/-!
# Davis' bounded universal quantifier

This file proves that bounded universal quantification preserves Diophantine sets:
if `S` is Diophantine, so is `{v | ∀ x < f v, (x, v) ∈ S}`.
-/

open Dioph Nat Sum

namespace CS

variable {α : Type} {n : ℕ}

/-- The bound `B` used in Davis' construction: it dominates the value of the majorant `q`
at the extreme arguments, as well as `y` and `u`. -/

theorem choose_eq_div_mod_gen (n u : ℕ) (hu : 2 ^ n < u) (k : ℕ) :
    ((u + 1) ^ n / u ^ k) % u = n.choose k := by
  set S : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (n + 1 - k), u ^ j * n.choose (j + k) with hS
  have hu0 : 0 < u := lt_of_le_of_lt (Nat.zero_le _) hu
  have hSlt : ∀ k, n.choose k < u := fun k => lt_of_le_of_lt (Nat.choose_le_two_pow n k) hu
  have hS0 : S 0 = (u + 1) ^ n := by
    simp only [hS, Nat.sub_zero, Nat.add_zero]
    rw [add_pow]; simp
  have hstep : ∀ k, k ≤ n → S k = n.choose k + u * S (k + 1) := by
    intro k hk
    have h1 : n + 1 - k = (n - k) + 1 := by omega
    have h2 : n + 1 - (k + 1) = n - k := by omega
    simp only [hS, h1, h2]
    rw [Finset.sum_range_succ', Finset.mul_sum, Nat.add_comm]
    congr 1
    · simp
    · exact Finset.sum_congr rfl fun i _ => by ring_nf
  have hSbig : ∀ k, n < k → S k = 0 := by
    intro k hk
    have h : n + 1 - k = 0 := by omega
    simp [hS, h]
  have hdiv : ∀ k, (u + 1) ^ n / u ^ k = S k := by
    intro k
    induction k with
    | zero => simp [hS0]
    | succ k ih =>
        rw [pow_succ, ← Nat.div_div_eq_div_mul, ih]
        rcases le_or_gt k n with hk | hk
        · rw [hstep k hk, Nat.add_mul_div_left _ _ hu0, Nat.div_eq_of_lt (hSlt k)]
          omega
        · rw [hSbig k hk, hSbig (k + 1) (by omega)]
          simp
  rw [hdiv]
  rcases le_or_gt k n with hk | hk
  · rw [hstep k hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hSlt k)]
  · rw [hSbig k hk, Nat.choose_eq_zero_of_lt hk]
    simp

/-- Explicit arithmetic formula for the binomial coefficient. -/
