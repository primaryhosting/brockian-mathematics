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

theorem rank_range_lt (hκ : κ.IsInaccessible) {a : ZFSet.{u}} (ha : a.rank < κ.ord)
    (f : Shrink.{u} ↥a → ZFSet.{u}) (hf : ∀ i, (f i).rank < κ.ord) :
    (ZFSet.range f).rank < κ.ord := by
  rw [ZFSet.rank_range]
  refine Cardinal.iSup_lt_ord_of_isRegular hκ.isRegular (mk_shrink_lt hκ a ha) fun i => ?_
  exact (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).succ_lt (hf i)

/-! ### `V κ` satisfies the axioms of ZFC (set-theoretic content) -/

/-- The finite von Neumann ordinals, used as a witness for the axiom of infinity. -/
