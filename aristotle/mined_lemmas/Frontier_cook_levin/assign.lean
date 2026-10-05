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

def assign (x w : List Bool) : ℕ → Bool :=
  fun i => if i < x.length then x.getD i false else w.getD (i - x.length) false

/-- A nondeterministic polynomial time verifier for the language `L`, given by a
polynomial size family of circuits. -/
structure NPVerifier (L : Set (List Bool)) where
  /-- length of the witness for inputs of length `n` -/
  wlen : ℕ → ℕ
  /-- the verifying circuit for inputs of length `n` -/
  circ : ℕ → Circ
  wf : ∀ n, Circ.WF (circ n)
  wlen_poly : Poly wlen
  size_poly : Poly (fun n => (circ n).length)
  spec : ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length = wlen x.length ∧
      Circ.eval (circ x.length) (assign x w) = true

/-- The class NP. -/
