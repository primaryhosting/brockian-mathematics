/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma stair_block_sub_self (h0 : 0 ∉ S) (hne : S.Nonempty) :
    Finset.Icc (mx S + 1 - stair S) (mx S) ⊆ S := by
  have h := Nat.findGreatest_spec (P := fun j => Finset.Icc (mx S + 1 - j) (mx S) ⊆ S)
    (m := 1) (n := mx S) (one_le_mx h0 hne) (by simpa using mx_mem S hne)
  exact h

