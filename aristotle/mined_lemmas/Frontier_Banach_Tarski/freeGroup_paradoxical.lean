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

theorem freeGroup_paradoxical :
    ∃ A : Fin 4 → Set (FreeGroup (Fin 2)),
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
      (⋃ i, A i) = Set.univ ∧
      Disjoint (A 0) (FreeGroup.of (0 : Fin 2) • A 1) ∧
      (A 0) ∪ (FreeGroup.of (0 : Fin 2) • A 1) = Set.univ ∧
      Disjoint (A 2) (FreeGroup.of (1 : Fin 2) • A 3) ∧
      (A 2) ∪ (FreeGroup.of (1 : Fin 2) • A 3) = Set.univ :=
  ⟨piece, pairwise_disjoint_piece, iUnion_piece, disjoint_piece_zero_smul,
    union_piece_zero_smul, disjoint_piece_two_smul, union_piece_two_smul⟩

end BT

/-
From the Hausdorff paradox to the Banach-Tarski paradox: the closed unit ball of `ℝ³`
is paradoxical for the action of the group of isometries.
-/
import RequestProject.BT.Sphere

open Set Function Metric
open scoped Pointwise

namespace BT

/-- The radial extension of a subset of the sphere: all points of the punctured closed unit
ball whose normalization lies in `A`. -/
