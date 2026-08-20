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

theorem XA_mono {A B : Set (FreeGroup (Fin 2))} (h : A ⊆ B) : XA A ⊆ XA B := by
  intro x hx
  obtain ⟨w, hw, m, hm, hwm⟩ := mem_XA.1 hx
  exact mem_XA.2 ⟨w, h hw, m, hm, hwm⟩

