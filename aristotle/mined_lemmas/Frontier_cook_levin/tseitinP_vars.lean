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

theorem tseitinP_vars {mode : ℕ → Option ProjBit} {gs : Circ} {M : ℕ} (hwf : Circ.WF gs)
    (hM : ∀ i, mode i = none → i < M) :
    ∀ c ∈ tseitinP mode gs, ∀ l ∈ c, l.1 < 2 * gs.length + 2 * M + 1 := by
  intro c hc l hl
  obtain ⟨j, g, hg, hc⟩ := mem_tseitinP hc
  have hjlt : j < gs.length := getElem?_lt hg
  cases g with
  | inp i =>
      cases hm : mode i with
      | some p =>
          simp only [gateClausesP, hm, List.mem_singleton] at hc
          subst hc
          simp only [List.mem_singleton] at hl
          subst hl
          simp only [gv]
          omega
      | none =>
          have hi : i < M := hM i hm
          simp only [gateClausesP, hm, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
            rcases hl with rfl | rfl <;> simp only [gv, iv] <;> omega
  | const b =>
      simp only [gateClausesP, List.mem_singleton] at hc
      subst hc
      simp only [List.mem_singleton] at hl
      subst hl
      simp only [gv]
      omega
  | neg k =>
      have hk : k < j := hwf j _ hg
      simp only [gateClausesP, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
        rcases hl with rfl | rfl <;> simp only [gv] <;> omega
  | conj k l' =>
      obtain ⟨hk, hl'⟩ : k < j ∧ l' < j := hwf j _ hg
      simp only [gateClausesP, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
        rcases hl with rfl | rfl | rfl <;> simp only [gv] <;> omega
  | disj k l' =>
      obtain ⟨hk, hl'⟩ : k < j ∧ l' < j := hwf j _ hg
      simp only [gateClausesP, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
        rcases hl with rfl | rfl | rfl <;> simp only [gv] <;> omega

