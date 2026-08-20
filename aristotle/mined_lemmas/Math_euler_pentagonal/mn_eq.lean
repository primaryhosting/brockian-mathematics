/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma mn_eq (S : Finset ℕ) (h : S.Nonempty) : mn S = S.min' h := dif_pos h

