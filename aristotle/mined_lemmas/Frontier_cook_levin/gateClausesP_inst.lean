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

theorem gateClausesP_inst (mode : ℕ → Option ProjBit) (x : List Bool) (j : ℕ) (g : Gate) :
    (gateClausesP mode j g).map (PClause.inst x) = gateClauses (modeVal mode x) j g := by
  cases g with
  | inp i =>
      cases hm : mode i with
      | none => simp [gateClausesP, gateClauses, modeVal, hm, PClause.inst, ProjBit.eval]
      | some p => simp [gateClausesP, gateClauses, modeVal, hm, PClause.inst, ProjBit.eval]
  | const b => simp [gateClausesP, gateClauses, PClause.inst, ProjBit.eval]
  | neg k => simp [gateClausesP, gateClauses, PClause.inst, ProjBit.eval]
  | conj k l => simp [gateClausesP, gateClauses, PClause.inst, ProjBit.eval]
  | disj k l => simp [gateClausesP, gateClauses, PClause.inst, ProjBit.eval]

