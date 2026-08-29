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

theorem bigOr_size (l : List Tree) (B : ℕ) (h : ∀ t ∈ l, t.size ≤ B) :
    (bigOr l).size ≤ (B + 1) * l.length + 1 := by
  induction l with
  | nil => simp [bigOr, size]
  | cons t ts ih =>
      have h1 : t.size ≤ B := h t (by simp)
      have h2 := ih (fun u hu => h u (by simp [hu]))
      simp only [bigOr, size, List.length_cons]
      have : (B + 1) * (ts.length + 1) + 1 = (B + 1) * ts.length + 1 + B + 1 := by ring
      omega

end Tree

end Frontier

import Mathlib

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Polynomial bounds

A tiny library about functions `ℕ → ℕ` that are bounded by a polynomial.
-/

namespace Frontier

/-- `Poly g` says that `g` is bounded by a polynomial. -/
