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

theorem mem_SATlang_example : ([true, false] : List Bool) ∈ SATlang := by
  refine ⟨fun _ => true, ?_⟩
  simp [decodeCNF, decodeClause, bitIdx, Std.Sat.CNF.eval, Std.Sat.CNF.Clause.eval]

end Frontier

import Mathlib
import RequestProject.Encoding
import RequestProject.Poly

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The class NP, the language SAT, and `SAT ∈ NP`

A language is a set of bit strings.  It is in `NP` when membership can be checked by a
polynomial size circuit reading the input word together with a polynomially long
witness word.
-/

namespace Frontier

open Std.Sat

/-- The circuit input assignment given by an input word `x` and a witness word `w`:
variables `0, …, |x|-1` carry the input, variables `|x|, |x|+1, …` the witness. -/
