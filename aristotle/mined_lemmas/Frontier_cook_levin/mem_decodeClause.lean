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

theorem mem_decodeClause {s : List Bool} {k i j : ℕ} {b : Bool} :
    (j, b) ∈ decodeClause s k i ↔ j < k ∧ s.getD (bitIdx k i j b) false = true := by
  simp only [decodeClause, List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨⟨j', hj', hmem⟩, hbit⟩
    have hjj : j' = j := by
      rcases hmem with h | h <;> · injection h with h1 _; exact h1.symm
    subst hjj
    exact ⟨hj', hbit⟩
  · rintro ⟨hj, hb⟩
    refine ⟨⟨j, hj, ?_⟩, hb⟩
    cases b
    · right; rfl
    · left; rfl

/-- Reading back an encoded formula gives a formula with the same value under every
assignment. -/
