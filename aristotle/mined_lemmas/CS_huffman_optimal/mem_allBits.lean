import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


@[simp] theorem mem_allBits {n : ℕ} {l : List Bool} : l ∈ allBits n ↔ l.length = n := by
  induction n generalizing l with
  | zero => simp [allBits, List.length_eq_zero_iff]
  | succ n ih =>
      cases l with
      | nil => simp [allBits]
      | cons b t =>
          cases b <;> simp [allBits, ih]

