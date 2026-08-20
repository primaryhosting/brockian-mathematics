/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma one_le_stair (h0 : 0 ∉ S) (hne : S.Nonempty) : 1 ≤ stair S := by
  unfold stair
  refine Nat.le_findGreatest (one_le_mx h0 hne) ?_
  simpa using mx_mem S hne

