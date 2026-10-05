/-
/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

namespace Frontier

open Filter Set

/-- A fixed nonprincipal ultrafilter on `ℕ`: an ultrafilter refining the cofinite filter. -/

lemma Ioi_mem_ramseyUF (x : ℕ) : Set.Ioi x ∈ ramseyUF :=
  ramseyUF_le_cofinite (by rw [Nat.cofinite_eq_atTop]; exact Filter.Ioi_mem_atTop x)

/-- The "ultrafilter colour" of a vertex `x`: the colour `b` such that
`{y | c x y = b}` belongs to the ultrafilter. -/
open scoped Classical in
