/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

open scoped Classical in
/-- The maximal cardinality of a chain in a finite partial order. -/

noncomputable def maxChainLen (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  (Finset.univ.filter (fun c : Finset α => IsChain (· ≤ ·) (c : Set α))).sup Finset.card

open scoped Classical in
/-- The height of `x`: the maximal cardinality of a chain all of whose elements are `≤ x`. -/
