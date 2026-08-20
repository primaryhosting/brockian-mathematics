import Mathlib
namespace MS2.CSLogic

/-- Cantor's diagonal argument: no map `α → (α → Bool)` is surjective. -/

theorem cantor_diagonal {α : Type*} (f : α → (α → Bool)) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨a, ha⟩ := hf (fun x => !(f x x))
  have : f a a = !(f a a) := congrFun ha a
  simp at this

/-- There is no injection from the powerset of `α` into `α`. -/
