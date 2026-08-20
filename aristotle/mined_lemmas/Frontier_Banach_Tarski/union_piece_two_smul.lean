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

theorem union_piece_two_smul :
    piece 2 ∪ (FreeGroup.of (1 : Fin 2) • piece 3) = Set.univ := by
  ext w
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hw : w ∈ piece 2
  · exact Or.inl hw
  · right
    rw [mem_piece_two] at hw
    rw [mem_smul_iff, mem_piece_three, toWord_inv_of_mul, if_neg hw]
    simp

/-- **Paradoxical decomposition of the free group of rank two.**  The free group `F` on two
generators `a = of 0` and `b = of 1` can be partitioned into four sets `A 0, A 1, A 2, A 3`
such that `A 0` together with `a • A 1` partitions `F`, and `A 2` together with `b • A 3`
partitions `F`. -/
