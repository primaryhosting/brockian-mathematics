/-
Auxiliary ordinal arithmetic: additive principality of `ω ^ γ` for the natural
(Hessenberg) sum `♯`.
-/
import Mathlib

open Ordinal NaturalOps Order

namespace Frontier

/-- Comparing two ordinals through their quotient and remainder by `P`. -/

theorem HydraStep.ord_lt {n : ℕ} {h h' : Hydra} (hs : HydraStep n h h') : ord h' < ord h := by
  induction hs with
  | chop l₁ l₂ =>
      simp only [ord_node, ordList_append, ordList_cons, ordList_nil, Ordinal.opow_zero]
      exact nadd_lt_nadd_left (by rw [one_nadd]; exact lt_succ _) _
  | copy l₁ l₂ m₁ m₂ =>
      have hsucc := ord_node_chop_head m₁ m₂
      have hkey : ordList (List.replicate n (Hydra.node (m₁ ++ m₂)))
          < ω ^ ord (Hydra.node (m₁ ++ .node [] :: m₂)) := by
        refine ordList_lt_opow ?_
        intro t ht
        rw [List.eq_of_mem_replicate ht, hsucc]
        exact lt_succ _
      simp only [ord_node, ordList_append, ordList_cons, nadd_assoc] at hkey ⊢
      exact nadd_lt_nadd_left (nadd_lt_nadd_right hkey _) _
  | ctx l₁ l₂ t t' _ ih =>
      simp only [ord_node, ordList_append, ordList_cons]
      refine nadd_lt_nadd_left (nadd_lt_nadd_right ?_ _) _
      exact (Ordinal.opow_lt_opow_iff_right one_lt_omega0).2 ih

/-- The hydra game relation is well founded. -/
