/-
Auxiliary ordinal arithmetic: additive principality of `ω ^ γ` for the natural
(Hessenberg) sum `♯`.
-/
import Mathlib

open Ordinal NaturalOps Order

namespace Frontier

/-- Comparing two ordinals through their quotient and remainder by `P`. -/

theorem ord_node_chop_head (m₁ m₂ : List Hydra) :
    ord (.node (m₁ ++ .node [] :: m₂)) = succ (ord (.node (m₁ ++ m₂))) := by
  simp only [ord_node, ordList_append, ordList_cons, ordList_nil, Ordinal.opow_zero]
  rw [one_nadd, nadd_succ]

/-- Every round of the hydra game strictly decreases the ordinal measure. -/
