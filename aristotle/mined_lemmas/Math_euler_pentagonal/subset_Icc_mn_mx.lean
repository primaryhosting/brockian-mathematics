/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma subset_Icc_mn_mx : S ⊆ Finset.Icc (mn S) (mx S) := by
  intro x hx
  simp only [Finset.mem_Icc]
  exact ⟨mn_le S hx, le_mx S hx⟩

