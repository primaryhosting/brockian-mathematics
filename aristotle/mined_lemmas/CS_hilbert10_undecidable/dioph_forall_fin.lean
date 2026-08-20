import RequestProject.DiophAux

/-!
# Davis' bounded universal quantifier

This file proves that bounded universal quantification preserves Diophantine sets:
if `S` is Diophantine, so is `{v | ∀ x < f v, (x, v) ∈ S}`.
-/

open Dioph Nat Sum

namespace CS

variable {α : Type} {n : ℕ}

/-- The bound `B` used in Davis' construction: it dominates the value of the majorant `q`
at the extreme arguments, as well as `y` and `u`. -/

theorem dioph_forall_fin {α : Type} : ∀ (n : ℕ) (S : Fin n → Set (α → ℕ)), (∀ i, Dioph (S i)) →
    Dioph {v | ∀ i, v ∈ S i} := by
  intro n
  induction n with
  | zero =>
      intro S _
      have he : {v : α → ℕ | ∀ i : Fin 0, v ∈ S i} = Set.univ := by ext v; simp
      rw [he]
      exact Dioph.of_no_dummies _ (Poly.const 0)
        (fun v => iff_of_true trivial (by simp [Poly.const_apply]))
  | succ n ih =>
      intro S d
      have hd := (ih (fun i => S i.succ) (fun i => d i.succ)).inter (d 0)
      refine Dioph.ext hd fun v => ?_
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      exact ⟨fun ⟨h1, h2⟩ i => Fin.cases h2 (fun j => h1 j) i, fun h => ⟨fun j => h j.succ, h 0⟩⟩

/-! ### Normalising the number of witness variables -/

/-- A polynomial depends on only finitely many of its variables. -/
