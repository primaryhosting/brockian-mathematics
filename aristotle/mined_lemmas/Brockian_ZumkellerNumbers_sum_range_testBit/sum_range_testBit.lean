import Mathlib

namespace Brockian.ZumkellerNumbers


lemma sum_range_testBit (k : ℕ) : ∀ x : ℕ, x < 2 ^ k →
    ∑ i ∈ Finset.range k, (if x.testBit i then 2 ^ i else 0) = x := by
  induction k with
  | zero => intro x hx; simp at hx ⊢; omega
  | succ n ih =>
    intro x hx
    rw [Finset.sum_range_succ']
    have hdiv : x / 2 < 2 ^ n := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      calc x < 2 ^ (n + 1) := hx
        _ = 2 ^ n * 2 := by ring
    have hIH := ih (x / 2) hdiv
    have hstep : ∀ i ∈ Finset.range n,
        (if x.testBit (i + 1) then 2 ^ (i + 1) else 0)
          = 2 * (if (x / 2).testBit i then 2 ^ i else 0) := by
      intro i _
      rw [Nat.testBit_add_one]
      by_cases h : (x / 2).testBit i <;> simp [h, pow_succ, Nat.mul_comm]
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, hIH]
    have h0 : (if x.testBit 0 then 2 ^ 0 else 0) = x % 2 := by
      rw [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
    rw [h0]
    omega

/-- The geometric sum of powers of two. -/
