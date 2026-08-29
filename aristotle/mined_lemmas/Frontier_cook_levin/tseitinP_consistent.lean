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

theorem tseitinP_consistent {mode : ℕ → Option ProjBit} {gs : Circ} (hwf : Circ.WF gs) :
    ∀ c ∈ tseitinP mode gs, PClause.Consistent c := by
  intro c hc
  obtain ⟨j, g, hg, hc⟩ := mem_tseitinP hc
  cases g with
  | inp i =>
      cases hm : mode i with
      | some p =>
          simp only [gateClausesP, hm, List.mem_singleton] at hc
          subst hc
          intro p1 h1 q1 h2 _
          simp only [List.mem_singleton] at h1 h2
          subst h1; subst h2; rfl
      | none =>
          simp only [gateClausesP, hm, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;>
            · intro p1 h1 q1 h2 hpq
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
              rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
                simp_all [gv, iv] <;> omega
  | const b =>
      simp only [gateClausesP, List.mem_singleton] at hc
      subst hc
      intro p1 h1 q1 h2 _
      simp only [List.mem_singleton] at h1 h2
      subst h1; subst h2; rfl
  | neg k =>
      have hk : k < j := hwf j _ hg
      simp only [gateClausesP, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;>
        · intro p1 h1 q1 h2 hpq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
          rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp_all [gv]
  | conj k l' =>
      obtain ⟨hk, hl'⟩ : k < j ∧ l' < j := hwf j _ hg
      simp only [gateClausesP, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · intro p1 h1 q1 h2 hpq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
          rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;> simp_all [gv]
  | disj k l' =>
      obtain ⟨hk, hl'⟩ : k < j ∧ l' < j := hwf j _ hg
      simp only [gateClausesP, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · intro p1 h1 q1 h2 hpq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
          rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;> simp_all [gv]

/-! ### The reduction -/

variable {L : Set (List Bool)}

/-- Which input variables of the verifying circuit are fixed, and to what. -/
