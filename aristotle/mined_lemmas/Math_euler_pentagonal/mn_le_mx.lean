/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma mn_le_mx (hne : S.Nonempty) : mn S ≤ mx S := le_mx S (mn_mem S hne)

