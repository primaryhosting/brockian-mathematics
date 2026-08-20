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

theorem Vs.found {κ : Cardinal.{u}} (a : Vs κ) (h : ∃ x : Vs κ, x.1 ∈ a.1) :
    ∃ x : Vs κ, x.1 ∈ a.1 ∧ ¬∃ y : Vs κ, y.1 ∈ x.1 ∧ y.1 ∈ a.1 := by
  obtain ⟨x0, hx0⟩ := h
  have hne : a.1 ≠ ∅ := fun hz => by
    rw [hz] at hx0
    exact ZFSet.notMem_empty _ hx0
  obtain ⟨y, hya, hinter⟩ := ZFSet.regularity a.1 hne
  refine ⟨⟨y, lt_trans (ZFSet.rank_lt_of_mem hya) a.2⟩, hya, ?_⟩
  rintro ⟨w, hwy, hwa⟩
  have : w.1 ∈ a.1 ∩ y := ZFSet.mem_inter.mpr ⟨hwa, hwy⟩
  rw [hinter] at this
  exact ZFSet.notMem_empty _ this

end Closure

/-! ### Evaluating the satisfaction relation in `V κ` -/

