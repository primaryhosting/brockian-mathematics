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

theorem XA_disjoint {A B : Set (FreeGroup (Fin 2))} (h : Disjoint A B) :
    Disjoint (XA A) (XA B) := by
  refine Set.disjoint_left.2 ?_
  intro x hx hx'
  obtain ⟨w, hw, m, hm, hwm⟩ := mem_XA.1 hx
  obtain ⟨v, hv, m', hm', hvm⟩ := mem_XA.1 hx'
  obtain ⟨rfl, -⟩ := M_unique hm hm' (hwm.trans hvm.symm)
  exact Set.disjoint_left.1 h hw hv

