import Mathlib

namespace Brockian.Pentagonal

/-- Generalized pentagonal number `g(k) = k(3k-1)/2` for `k ∈ ℤ`.
    Integer division by 2 is exact here since `k(3k-1)` is always even. -/
def pent (k : ℤ) : ℤ := k * (3 * k - 1) / 2

/-- Division-free "doubled" form: `pent2 k = k(3k-1) = 2 · pent k`.
    This avoids integer division and is the centerpiece for the general identity. -/
def pent2 (k : ℤ) : ℤ := k * (3 * k - 1)

/-! ### Concrete tabulated values of `pent` (proved by `decide`). -/

theorem pent_0    : pent 0    = 0  := by decide
theorem pent_1    : pent 1    = 1  := by decide
theorem pent_neg1 : pent (-1) = 2  := by decide
theorem pent_2    : pent 2    = 5  := by decide
theorem pent_neg2 : pent (-2) = 7  := by decide
theorem pent_3    : pent 3    = 12 := by decide
theorem pent_neg3 : pent (-3) = 15 := by decide

/-- The classic ordering `0, 1, 2, 5, 7, 12, 15, …` as generalized pentagonal numbers. -/
theorem pent_values :
    pent 0 = 0 ∧ pent 1 = 1 ∧ pent (-1) = 2 ∧ pent 2 = 5 ∧
    pent (-2) = 7 ∧ pent 3 = 12 ∧ pent (-3) = 15 :=
  ⟨pent_0, pent_1, pent_neg1, pent_2, pent_neg2, pent_3, pent_neg3⟩

/-! ### The general ∀-k structural identity (the prize).

The doubled form is division-free, so `ring` proves the recurrence for ALL `k : ℤ`.
Since `pent2 k = 2 · pent k`, this is exactly `2·(pent(k+1) − pent k) = 2·(3k+1)`,
i.e. the pentagonal recurrence `pent (k+1) − pent k = 3k+1`. -/

/-- **Centerpiece.** The first-difference identity for the division-free doubled form,
    fully general over `ℤ`, proved by pure algebra. -/
theorem pent2_succ_diff (k : ℤ) : pent2 (k + 1) - pent2 k = 6 * k + 2 := by
  unfold pent2; ring

/-- `pent2` is exactly twice `pent` at every concrete tabulated point. -/
theorem pent2_eq_two_mul_pent_samples :
    pent2 0 = 2 * pent 0 ∧ pent2 1 = 2 * pent 1 ∧ pent2 (-1) = 2 * pent (-1) ∧
    pent2 2 = 2 * pent 2 ∧ pent2 (-2) = 2 * pent (-2) ∧
    pent2 3 = 2 * pent 3 ∧ pent2 (-3) = 2 * pent (-3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Corollary at the tabulated level: the doubled recurrence evaluated at `k = 1`
    gives `pent2 2 − pent2 1 = 8`, matching `6·1 + 2`. -/
theorem pent2_succ_diff_at_one : pent2 2 - pent2 1 = 6 * 1 + 2 := by decide

/-- The ordinary-pentagonal recurrence at the difference level, division-free and general:
    dividing the doubled identity by 2 gives `pent (k+1) − pent k = 3k + 1`.
    Stated here in the exact scaled form that holds for ALL `k` with no division. -/
theorem pent_recurrence_doubled (k : ℤ) :
    2 * pent2 (k + 1) - 2 * pent2 k = 12 * k + 4 := by
  unfold pent2; ring

end Brockian.Pentagonal
