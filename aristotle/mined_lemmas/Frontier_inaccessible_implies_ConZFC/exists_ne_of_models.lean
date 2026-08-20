/-
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
This file formalizes the statement that a (strongly) inaccessible cardinal `κ` yields a model of
`ZFC`, namely the rank-initial segment `V κ = {x : ZFSet | rank x < κ.ord}` of the von Neumann
hierarchy, and deduces the semantic consistency statement `Con(ZFC)` (i.e. satisfiability of the
first-order theory `ZFCTheory`) from the existence of an inaccessible cardinal.
-/

universe u

namespace Frontier

open FirstOrder Language Cardinal Ordinal ZFSet

/-! ## The first-order language of set theory -/

/-- The relations of the language of set theory: a single binary relation `∈`. -/
inductive memRel : ℕ → Type
  | mem : memRel 2

/-- The first-order language of set theory: one binary relation symbol, no functions. -/

theorem exists_ne_of_models [M ⊨ ZFCTheory] : ∃ x y : M, x ≠ y := by
  have hinf : M ⊨ infAx :=
    Theory.realize_sentence_of_mem ZFCTheory (by
      simp only [ZFCTheory, Set.union_assoc, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      tauto)
  obtain ⟨i, ⟨e, hei, he⟩, _⟩ := realize_infAx_iff.mp hinf
  refine ⟨e, i, fun h => ?_⟩
  exact he e (h ▸ hei)

end Faithful

/-! ### `V κ` models each axiom -/

section Models

variable {κ : Cardinal.{u}}

