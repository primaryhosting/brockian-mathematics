import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem XA_union (A B : Set (FreeGroup (Fin 2))) : XA (A ∪ B) = XA A ∪ XA B := by
  ext x
  simp only [mem_XA, Set.mem_union]
  constructor
  · rintro ⟨w, (hw | hw), m, hm, hwm⟩
    · exact Or.inl ⟨w, hw, m, hm, hwm⟩
    · exact Or.inr ⟨w, hw, m, hm, hwm⟩
  · rintro (⟨w, hw, m, hm, hwm⟩ | ⟨w, hw, m, hm, hwm⟩)
    · exact ⟨w, Or.inl hw, m, hm, hwm⟩
    · exact ⟨w, Or.inr hw, m, hm, hwm⟩

