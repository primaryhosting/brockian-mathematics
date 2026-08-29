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

theorem red_mem_SAT (V : NPVerifier L) (x : List Bool) : x ∈ L ↔ red V x ∈ SATlang := by
  rw [← red_spec V x, red_eq, SATlang, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by
      rw [eval_decode_encode (by simp [redK])
        (by simpa using redP_length V x.length) (inst_vars (redP_vars V x.length)) a]
      exact ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [eval_decode_encode (by simp [redK])
      (by simpa using redP_length V x.length) (inst_vars (redP_vars V x.length)) a] at ha
    exact ha

