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

noncomputable def longestChainCard (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  chainSup (Finset.univ : Finset α)

/-- A finite family of subsets of `α` is an *antichain cover* when each member is an
antichain and every element lies in some member. -/
