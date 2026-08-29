/-
# Szemeredi Regularity
Category: Frontier Abel
Target: Frontier.szemeredi_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Szemeredi Regularity
Category: Frontier Abel
Target: Frontier.szemeredi_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Frontier

open scoped Classical in
/-- The edge density between two finsets of vertices `u`, `v` of a graph `G`: the number of
adjacent pairs `(a, b) ∈ u ×ˢ v`, divided by `#u * #v`. -/

noncomputable def edgeDens {α : Type*} (G : SimpleGraph α) (u v : Finset α) : ℝ :=
  (#{e ∈ u ×ˢ v | G.Adj e.1 e.2} : ℝ) / (#u * #v)

/-- A pair `(u, v)` of finsets of vertices is `ε`-regular (`ε`-uniform) for `G` when the edge
density between any pair of subsets `u' ⊆ u`, `v' ⊆ v` that are not too small (of size at least
`ε * #u` resp. `ε * #v`) is within `ε` of the edge density between `u` and `v`. -/
