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

theorem eval_decode_encode {k : ℕ} {f : CNF ℕ} (hk : 0 < k) (hlen : f.length ≤ k)
    (hvar : ∀ c ∈ f, ∀ l ∈ c, l.1 < k) (a : ℕ → Bool) :
    CNF.eval a (decodeCNF (encodeCNF k f)) = CNF.eval a f := by
  set s := encodeCNF k f with hs
  have hdec : decodeCNF s = (List.range k).map (decodeClause s k) := by
    rw [decodeCNF, hs, sqrt_encode]
  -- value of a decoded clause
  have hclause : ∀ i, i < k → ∀ c, f[i]? = some c →
      CNF.Clause.eval a (decodeClause s k i) = CNF.Clause.eval a c := by
    intro i hi c hc
    refine clause_eval_congr a ?_
    rintro ⟨j, b⟩
    rw [mem_decodeClause]
    constructor
    · rintro ⟨hj, hb⟩
      rw [hs, encodeCNF_getD k f (bitIdx_lt b hi hj), encodeBit_bitIdx k f b hj, hc] at hb
      simpa using hb
    · intro hmem
      have hjk : j < k := hvar c (List.mem_of_getElem? hc) (j, b) hmem
      refine ⟨hjk, ?_⟩
      rw [hs, encodeCNF_getD k f (bitIdx_lt b hi hjk), encodeBit_bitIdx k f b hjk, hc]
      simpa using hmem
  -- a padding row is a tautology
  have hpad : ∀ i, i < k → f[i]? = none → CNF.Clause.eval a (decodeClause s k i) = true := by
    intro i hi hc
    have hmem : ∀ b : Bool, (0, b) ∈ decodeClause s k i := by
      intro b
      rw [mem_decodeClause]
      refine ⟨hk, ?_⟩
      rw [hs, encodeCNF_getD k f (bitIdx_lt b hi hk), encodeBit_bitIdx k f b hk, hc]
      simp
    simp only [CNF.Clause.eval, List.any_eq_true]
    exact ⟨(0, a 0), hmem (a 0), by simp⟩
  rw [Bool.eq_iff_iff, eval_eq_true_iff, eval_eq_true_iff, hdec]
  constructor
  · intro h c hc
    obtain ⟨i, hi, hget⟩ : ∃ i, i < f.length ∧ f[i]? = some c := by
      obtain ⟨i, hi⟩ := List.mem_iff_getElem.mp hc
      exact ⟨i, hi.1, by rw [List.getElem?_eq_getElem hi.1, hi.2]⟩
    have hik : i < k := lt_of_lt_of_le hi hlen
    rw [← hclause i hik c hget]
    exact h _ (List.mem_map_of_mem (by simpa using hik))
  · intro h c hc
    simp only [List.mem_map, List.mem_range] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    cases hget : f[i]? with
    | none => exact hpad i hi hget
    | some c' =>
        rw [hclause i hi c' hget]
        exact h c' (List.mem_of_getElem? hget)

/-! ### Parametric encoding

For the reduction we need the bits of the encoding to depend on the input word only
through single bits ("projections"). -/

/-- The polarity attached to the variable `j` in a parametric clause, if any. -/
