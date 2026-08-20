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

theorem models_ZFCTheory {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) : (Vs κ) ⊨ ZFCTheory := by
  refine ⟨fun φ hφ => ?_⟩
  rcases hφ with (hφ | hφ) | hφ
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact models_extAx
    · exact models_foundAx
    · exact models_pairAx hκ
    · exact models_unionAx
    · exact models_powerAx hκ
    · exact models_infAx hκ
    · exact models_acAx hκ
  · obtain ⟨p, rfl⟩ := hφ
    exact models_sepAx p.2
  · obtain ⟨p, rfl⟩ := hφ
    exact models_collAx hκ p.2

instance instNonemptyVs {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) : Nonempty (Vs κ) :=
  ⟨⟨∅, by
    rw [ZFSet.rank_empty]
    exact (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).bot_lt⟩⟩

/-- **An inaccessible cardinal yields a model of ZFC**: if there is a (strongly) inaccessible
cardinal, then the first-order theory `ZFCTheory` is satisfiable, i.e. `Con(ZFC)` holds
(semantically). -/
