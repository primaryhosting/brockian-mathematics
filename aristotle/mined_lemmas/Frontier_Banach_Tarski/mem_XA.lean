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

theorem mem_XA {A : Set (FreeGroup (Fin 2))} {x : E} :
    x ∈ XA A ↔ ∃ w ∈ A, ∃ m ∈ M, phi w m = x := by
  simp [XA, Set.mem_smul_set, eq_comm]

