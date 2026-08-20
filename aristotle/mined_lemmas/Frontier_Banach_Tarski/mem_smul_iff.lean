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

theorem mem_smul_iff {g w : FreeGroup (Fin 2)} {A : Set (FreeGroup (Fin 2))} :
    w ∈ g • A ↔ g⁻¹ * w ∈ A := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]

