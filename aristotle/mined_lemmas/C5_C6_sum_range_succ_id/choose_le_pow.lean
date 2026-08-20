import Mathlib
open Finset
namespace C5.C6

/-- Gauss' summation formula, in the doubled form `2 * ∑_{i<n+1} i = n(n+1)`.
See `Finset.sum_range_id_mul_two` in Mathlib. -/

theorem choose_le_pow (n k : ℕ) : n.choose k ≤ 2^n := by
  rcases le_or_gt k n with hk | hk
  · calc n.choose k ≤ ∑ i ∈ range (n+1), n.choose i :=
          Finset.single_le_sum (f := fun i => n.choose i) (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
      _ = 2 ^ n := Nat.sum_range_choose n
  · simp [Nat.choose_eq_zero_of_lt hk]

/-- Factorials are positive (`Nat.factorial_pos`). -/
