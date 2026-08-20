/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma two_mul_sum_Icc_add (a d : ℕ) :
    2 * (∑ i ∈ Finset.Icc a (a + d), i) = (2 * a + d) * (d + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show a + (d + 1) = (a + d) + 1 from rfl, Finset.sum_Icc_succ_top (by omega)]
    rw [Nat.mul_add, ih]
    ring

