import Mathlib
namespace MS.Foundations


private theorem expTail_lt_one (n : ℕ) (hn : 1 ≤ n) :
    (n ! : ℝ) * (Real.exp 1 - expPartial n) < 1 := by
  have hb := Real.exp_bound (x := 1) (by norm_num) (n := n + 1) (by omega)
  have hfn : (0 : ℝ) < (n ! : ℝ) := by positivity
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hfac : (((n + 1)! : ℕ) : ℝ) = ((n : ℝ) + 1) * (n ! : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have key : Real.exp 1 - expPartial n ≤ ((n : ℝ) + 2) / ((((n + 1)! : ℕ) : ℝ) * ((n : ℝ) + 1)) := by
    refine (le_abs_self _).trans (hb.trans_eq ?_)
    push_cast
    norm_num
    ring
  have hlt : (n ! : ℝ) * (((n : ℝ) + 2) / ((((n + 1)! : ℕ) : ℝ) * ((n : ℝ) + 1))) < 1 := by
    rw [hfac, show (n ! : ℝ) * (((n : ℝ) + 2) / (((n : ℝ) + 1) * (n ! : ℝ) * ((n : ℝ) + 1)))
        = ((n : ℝ) + 2) / (((n : ℝ) + 1) * ((n : ℝ) + 1)) by field_simp,
      div_lt_one (by positivity)]
    nlinarith
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left key hfn.le) hlt

/-- `n! * S_{n+1}` is a natural number. -/
