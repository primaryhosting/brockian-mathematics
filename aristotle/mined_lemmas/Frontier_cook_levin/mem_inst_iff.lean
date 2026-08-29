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

theorem mem_inst_iff (x : List Bool) (c : PClause) (j : ℕ) (b : Bool)
    (hcon : PClause.Consistent c) :
    ((j, b) ∈ PClause.inst x c) ↔
      (match lookupVar c j with
        | some p => p.eval x = b
        | none => False) := by
  simp only [PClause.inst, List.mem_map]
  cases hl : lookupVar c j with
  | none =>
      simp only [iff_false]
      rintro ⟨q, hq, hqe⟩
      have hq1 : q.1 = j := by simpa using congrArg Prod.fst hqe
      rw [lookupVar] at hl
      cases hf : c.find? (fun p => decide (p.1 = j)) with
      | none =>
          have := List.find?_eq_none.mp hf q hq
          simp [hq1] at this
      | some p => rw [hf] at hl; simp at hl
  | some p =>
      rw [lookupVar] at hl
      cases hf : c.find? (fun p => decide (p.1 = j)) with
      | none => rw [hf] at hl; simp at hl
      | some q =>
          rw [hf] at hl
          simp only [Option.map_some] at hl
          have hqmem : q ∈ c := List.mem_of_find?_eq_some hf
          have hq1 : q.1 = j := by simpa using List.find?_some hf
          have hqp : q.2 = p := Option.some.inj hl
          subst hqp
          constructor
          · rintro ⟨r, hr, hre⟩
            have hr1 : r.1 = j := by simpa using congrArg Prod.fst hre
            have hr2 : r.2 = q.2 := hcon r hr q hqmem (by rw [hr1, hq1])
            have : r.2.eval x = b := by simpa using congrArg Prod.snd hre
            rwa [hr2] at this
          · intro hb
            exact ⟨q, hqmem, by rw [hq1, hb]⟩

/-- The projection bit recording the occurrence of the literal `(j, b)` in the
parametric clause `c`. -/
