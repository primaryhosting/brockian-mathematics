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

theorem Frontier.isRegularPair_iff (ε : ℝ) (u v : Finset α) :
    Frontier.IsRegularPair G ε u v ↔ G.IsUniform ε u v := by
  constructor
  · intro h u' hu' v' hv' hu hv
    simpa [Frontier.edgeDens_eq] using h u' hu' v' hv' hu hv
  · intro h u' hu' v' hv' hu hv
    simpa [Frontier.edgeDens_eq] using h hu' hv' hu hv

end Auxiliary

namespace Frontier

open scoped Classical in
/-- **Szemerédi's Regularity Lemma.**

For every `ε > 0` and every `l : ℕ` there is a bound `M`, depending only on `ε` and `l`, such that
every finite simple graph `G` on at least `l` vertices admits a partition of its vertex set into
`parts` such that:

* every part is nonempty and every vertex lies in exactly one part (so `parts` is a partition);
* the partition is *equitable*: any two parts differ in size by at most one;
* the number of parts is between `l` and `M`;
* all but at most `ε * #parts ^ 2` of the ordered pairs of distinct parts are `ε`-regular.
-/
