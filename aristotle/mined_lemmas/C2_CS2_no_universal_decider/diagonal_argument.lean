import Mathlib
namespace C2.CS2

/-- No boolean equals its own negation. -/

theorem diagonal_argument {α : Type*} (f : α → (α → Bool)) : ¬ Function.Surjective f := by
  intro hs
  obtain ⟨a, ha⟩ := hs (fun x => !(f x x))
  have h := congrFun ha a
  simp at h

/-- Pigeonhole principle for functions between finite types. -/
