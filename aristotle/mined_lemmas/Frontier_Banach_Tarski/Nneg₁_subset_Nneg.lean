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

theorem Nneg₁_subset_Nneg : Nneg₁ ⊆ Nneg := by
  rintro w ⟨n, _, hn⟩
  exact ⟨n, hn⟩

/-- Every element lies in one of the four pieces. -/
