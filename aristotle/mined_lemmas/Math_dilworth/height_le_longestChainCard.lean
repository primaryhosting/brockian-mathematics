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

lemma height_le_longestChainCard (x : α) : height x ≤ longestChainCard α :=
  chainSup_mono (Finset.filter_subset _ _)

