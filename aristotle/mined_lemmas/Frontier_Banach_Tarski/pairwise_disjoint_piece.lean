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

theorem pairwise_disjoint_piece : ∀ i j : Fin 4, i ≠ j → Disjoint (piece i) (piece j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;>
    first
      | exact disjoint_01 | exact disjoint_02 | exact disjoint_03
      | exact disjoint_12 | exact disjoint_13 | exact disjoint_23
      | exact disjoint_01.symm | exact disjoint_02.symm | exact disjoint_03.symm
      | exact disjoint_12.symm | exact disjoint_13.symm | exact disjoint_23.symm

