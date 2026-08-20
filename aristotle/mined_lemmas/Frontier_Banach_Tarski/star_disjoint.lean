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

theorem star_disjoint {A B : Set E} (h : Disjoint A B) : Disjoint (star A) (star B) := by
  refine Set.disjoint_left.2 ?_
  rintro y ⟨-, -, hy⟩ ⟨-, -, hy'⟩
  exact Set.disjoint_left.1 h hy hy'

/-- Equidecomposability of subsets of the sphere extends radially. -/
