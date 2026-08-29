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

theorem satLitTree_eval (s w : List Bool) {k i j : ℕ} (hk : k = Nat.sqrt (s.length / 2))
    (hi : i < k) (hj : j < k) :
    (satLitTree s.length k i j).eval (assign s w)
      = (s.getD (bitIdx k i j true) false && w.getD j false ||
          s.getD (bitIdx k i j false) false && !(w.getD j false)) := by
  simp [satLitTree, Tree.eval, assign_bit s w true hk hi hj, assign_bit s w false hk hi hj,
    assign_wit s w j]

/-- The verifying circuit for SAT accepts `(s, w)` exactly when the assignment described
by `w` satisfies the formula denoted by `s`. -/
