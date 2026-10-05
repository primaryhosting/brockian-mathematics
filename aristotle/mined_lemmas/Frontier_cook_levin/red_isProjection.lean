import Mathlib
import RequestProject.Hardness

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Cook–Levin theorem

`SAT` is NP-complete:

* `SAT ∈ NP`, and
* every language in `NP` reduces to `SAT`.

Here languages are sets of bit strings; a language is in `NP` when it is decided by a
family of polynomial size Boolean circuits reading the input word together with a
witness word of polynomial length (`Frontier.InNP`).  `SAT` is the set of bit strings
whose associated CNF formula is satisfiable (`Frontier.SATlang`), the association being
the occurrence-matrix encoding of `Frontier.decodeCNF`.

The reductions produced here are *projections*: each output bit is a constant, or a bit
of the input word, or the negation of a bit of the input word, and the number of output
bits is polynomial in the length of the input word (`Frontier.IsProjectionReduction`).
In particular they are computable by polynomial size circuits.

The circuit families witnessing membership in `NP` are not required to be uniformly
generated, so `Frontier.InNP` is the non-uniform version of `NP`; correspondingly the
reductions produced by the hardness proof are non-uniform (but they are projections,
which is a much more restrictive class than polynomial time computable maps).
-/

namespace Frontier

/-- `L₁` reduces to `L₂` by a projection reduction. -/

theorem red_isProjection (V : NPVerifier L) : IsProjectionReduction (red V) := by
  refine ⟨redBits V, fun x => rfl, ?_⟩
  refine Poly.mono (g := fun n => 2 * redK V n * redK V n) ?_ ?_
  · exact ((Poly.const 2).mul (redK_poly V)).mul (redK_poly V)
  · intro n
    simp [redBits, encodeCNFP]

end Frontier

import Mathlib
import RequestProject.Tseitin

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Encoding CNF formulas as bit strings

A bit string of length `ℓ` is read as a `k × k` occurrence matrix of literals, where
`k = ⌊√(ℓ/2)⌋`: the two bits at positions `bitIdx k i j true` and `bitIdx k i j false`
say whether the literals `(j, true)` and `(j, false)` occur in clause `i`.
So a bit string always denotes a CNF formula with `k` clauses over the `k` variables
`0, …, k-1`.

Conversely `encodeCNF k f` writes a formula with at most `k` clauses over the variables
`0, …, k-1` as a bit string of length `2 * k * k`; rows beyond the clauses of `f` are
filled with all-ones rows, i.e. with tautological clauses.
-/

namespace Frontier

open Std.Sat

/-- Position of the bit recording the occurrence of the literal `(j, b)` in clause `i`. -/
