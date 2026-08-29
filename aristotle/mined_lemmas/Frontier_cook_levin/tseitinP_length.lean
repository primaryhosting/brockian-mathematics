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

theorem tseitinP_length (mode : ℕ → Option ProjBit) (gs : Circ) :
    (tseitinP mode gs).length ≤ 3 * gs.length := by
  rw [tseitinP, List.length_flatMap]
  have h : ∀ y ∈ (gs.zipIdx.map (fun p => (gateClausesP mode p.2 p.1).length)), y ≤ 3 := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨p, _, rfl⟩ := hy
    exact gateClausesP_length mode p.2 p.1
  refine le_trans (List.sum_le_card_nsmul _ 3 h) ?_
  simp [mul_comm]

