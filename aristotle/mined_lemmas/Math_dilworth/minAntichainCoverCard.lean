import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

namespace Math

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The largest cardinality of a chain contained in the finite set `t`. -/

noncomputable def minAntichainCoverCard (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  sInf {n | ∃ F : Finset (Finset α), F.card ≤ n ∧ IsAntichainCover F}

/-- The `height` of `x` is the length of a longest chain in the down-set of `x`. -/
