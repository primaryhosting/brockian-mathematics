/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma one_le_mx (h0 : 0 ∉ S) (hne : S.Nonempty) : 1 ≤ mx S := by
  rcases Nat.eq_zero_or_pos (mx S) with h | h
  · exact absurd (h ▸ mx_mem S hne) h0
  · exact h

