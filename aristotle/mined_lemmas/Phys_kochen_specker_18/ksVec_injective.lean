/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Statement: An explicit 18-vector Kochen–Specker set in ℝ⁴ has no {0,1} coloring.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Statement: An explicit 18-vector Kochen–Specker set in ℝ⁴ has no {0,1} coloring.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set,
with integer entries. -/

theorem ksVec_injective : Function.Injective ksVec := by
  have h : Function.Injective ksVecZ := by decide
  intro i j hij
  refine h ?_
  funext k
  have := congrFun hij k
  simpa [ksVec] using this

/-- **Kochen–Specker (18 vectors, 9 contexts).**
The explicit 18-vector set `ksVec` in `ℝ⁴` admits no `{0,1}`-coloring assigning
value `1` to exactly one vector of every quadruple of pairwise distinct, pairwise
orthogonal vectors of the set. -/
