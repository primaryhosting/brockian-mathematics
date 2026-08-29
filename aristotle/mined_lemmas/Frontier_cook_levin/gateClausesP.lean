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

def gateClausesP (mode : ℕ → Option ProjBit) (j : ℕ) : Gate → PCnf
  | .inp i =>
      match mode i with
      | some p => [[(gv j, p)]]
      | none => [[(gv j, .cst false), (iv i, .cst true)], [(gv j, .cst true), (iv i, .cst false)]]
  | .const b => [[(gv j, .cst b)]]
  | .neg k => [[(gv j, .cst false), (gv k, .cst false)], [(gv j, .cst true), (gv k, .cst true)]]
  | .conj k l =>
      [[(gv j, .cst false), (gv k, .cst true)], [(gv j, .cst false), (gv l, .cst true)],
        [(gv j, .cst true), (gv k, .cst false), (gv l, .cst false)]]
  | .disj k l =>
      [[(gv j, .cst true), (gv k, .cst false)], [(gv j, .cst true), (gv l, .cst false)],
        [(gv j, .cst false), (gv k, .cst true), (gv l, .cst true)]]

/-- Parametric version of `tseitin`. -/
