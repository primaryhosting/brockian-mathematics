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

theorem satTree_size (l : ℕ) :
    (satTree l).size ≤ (9 * Nat.sqrt (l / 2) + 2) * Nat.sqrt (l / 2) + 1 := by
  set k := Nat.sqrt (l / 2)
  refine le_trans (Tree.bigAnd_size _ (9 * k + 1) ?_) ?_
  · intro t ht
    simp only [List.mem_map, List.mem_range] at ht
    obtain ⟨i, _, rfl⟩ := ht
    refine le_trans (Tree.bigOr_size _ 8 ?_) ?_
    · intro u hu
      simp only [List.mem_map, List.mem_range] at hu
      obtain ⟨j, _, rfl⟩ := hu
      exact le_of_eq (satLitTree_size l k i j)
    · simp only [List.length_map, List.length_range]
      omega
  · simp only [List.length_map, List.length_range]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right k (by omega)) 1

/-- Evaluation of the verifying formula. -/
