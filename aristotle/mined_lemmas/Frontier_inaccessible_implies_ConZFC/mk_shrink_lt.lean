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

theorem mk_shrink_lt (hκ : κ.IsInaccessible) (a : ZFSet.{u}) (ha : a.rank < κ.ord) :
    #(Shrink.{u} ↥a) < κ := by
  have h1 : #(↥a) ≤ #{x : ZFSet.{u} // x.rank < a.rank} := by
    apply Cardinal.mk_le_of_injective
      (f := fun z : ↥a => (⟨z.1, ZFSet.rank_lt_of_mem z.2⟩ : {x : ZFSet.{u} // x.rank < a.rank}))
    intro x y h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  have h2 := lt_of_le_of_lt h1 (mk_rank_lt_lt hκ a.rank ha)
  have h3 : Cardinal.lift.{u+1,u} #(Shrink.{u} ↥a) = #(↥a) := by
    rw [Cardinal.lift_mk_shrink']
    exact Cardinal.lift_id'.{u, u+1} _
  rw [← h3] at h2
  exact Cardinal.lift_lt.mp h2

/-- The range of a family indexed by (the elements of) a set of `V κ` lies in `V κ`. -/
