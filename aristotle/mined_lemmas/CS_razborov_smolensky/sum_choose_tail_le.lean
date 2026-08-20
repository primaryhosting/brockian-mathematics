import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem sum_choose_tail_le (m D : ℕ) :
    ∑ i ∈ range (m + D + 1), (2 * m + 1).choose i ≤ 4 ^ m + D * ((2 * m + 1).choose m) := by
  have hsplit : ∑ i ∈ range (m + D + 1), (2 * m + 1).choose i
      = (∑ i ∈ range (m + 1), (2 * m + 1).choose i)
        + ∑ i ∈ Ico (m + 1) (m + D + 1), (2 * m + 1).choose i := by
    rw [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le (m + 1)) (by omega)).symm
  rw [hsplit, Nat.sum_range_choose_halfway m]
  gcongr
  calc ∑ i ∈ Ico (m + 1) (m + D + 1), (2 * m + 1).choose i
      ≤ ∑ _i ∈ Ico (m + 1) (m + D + 1), (2 * m + 1).choose m := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have := Nat.choose_le_middle i (2 * m + 1)
        simpa [Nat.add_mul_div_left, Nat.mul_add_div] using this
    _ = D * ((2 * m + 1).choose m) := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
        congr 1
        omega

/-- Consequence: if `32 D² ≤ n+1` then `4 D C(n,i) ≤ 2^n`. -/
