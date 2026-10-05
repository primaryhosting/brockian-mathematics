/-
Auxiliary ordinal arithmetic: additive principality of `ω ^ γ` for the natural
(Hessenberg) sum `♯`.
-/
import Mathlib

open Ordinal NaturalOps Order

namespace Frontier

/-- Comparing two ordinals through their quotient and remainder by `P`. -/

theorem ordList_lt_opow {l : List Hydra} {γ : Ordinal} (h : ∀ t ∈ l, ord t < γ) :
    ordList l < ω ^ γ := by
  induction l with
  | nil => simpa using Ordinal.opow_pos γ omega0_pos
  | cons t ts ih =>
      rw [ordList_cons]
      refine nadd_lt_opow ?_ (ih fun x hx => h x (List.mem_cons_of_mem _ hx))
      exact (Ordinal.opow_lt_opow_iff_right one_lt_omega0).2 (h t List.mem_cons_self)

end Hydra

/-- One round of the hydra game, in which the hydra regrows `n` copies.

* `chop`: Hercules removes a head attached directly to the root; nothing regrows.
* `copy`: Hercules removes a head at distance two from the root; the root then grows `n`
  copies of the head's parent, with the head removed.
* `ctx`: the round takes place inside one of the subtrees hanging from the root. -/
inductive HydraStep : ℕ → Hydra → Hydra → Prop
  | chop (n : ℕ) (l₁ l₂ : List Hydra) :
      HydraStep n (.node (l₁ ++ .node [] :: l₂)) (.node (l₁ ++ l₂))
  | copy (n : ℕ) (l₁ l₂ m₁ m₂ : List Hydra) :
      HydraStep n (.node (l₁ ++ .node (m₁ ++ .node [] :: m₂) :: l₂))
        (.node (l₁ ++ List.replicate n (.node (m₁ ++ m₂)) ++ l₂))
  | ctx (n : ℕ) (l₁ l₂ : List Hydra) (t t' : Hydra) :
      HydraStep n t t' → HydraStep n (.node (l₁ ++ t :: l₂)) (.node (l₁ ++ t' :: l₂))

open Hydra

/-- Removing a head from the children of a node decreases its measure by exactly one. -/
