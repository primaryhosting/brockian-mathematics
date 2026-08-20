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

theorem XA_univ : XA Set.univ = SX := by
  apply Set.Subset.antisymm (XA_subset _)
  intro x hx
  obtain ⟨w, m, hm, hwm⟩ := exists_mem_M hx
  exact mem_XA.2 ⟨w, mem_univ w, m, hm, hwm⟩

