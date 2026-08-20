import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order Set

/-! ## Cardinal arithmetic of the von Neumann hierarchy below an inaccessible -/

variable {κ : Cardinal.{u}}

/-- Below an inaccessible cardinal `κ`, all the beth-numbers are smaller than `κ`. -/

theorem range_mem_vonNeumann (hκ : κ.IsInaccessible) {x : ZFSet.{u}} (hx : x ∈ vonNeumann κ.ord)
    (f : ↥x → ZFSet.{u}) (hf : ∀ i, f i ∈ vonNeumann κ.ord) :
    ZFSet.range f ∈ vonNeumann κ.ord := by
  rw [ZFSet.mem_vonNeumann, ZFSet.rank_range]
  have he : (⨆ i : ↥x, succ (rank (f i)))
      = ⨆ j : Shrink.{u} ↥x, succ (rank (f ((equivShrink _).symm j))) :=
    (Equiv.iSup_comp (g := fun i : ↥x => succ (rank (f i)))
      (equivShrink _).symm).symm
  rw [he]
  refine Ordinal.iSup_lt_ord (f := fun j => succ (rank (f ((equivShrink _).symm j)))) ?_ ?_
  · rw [hκ.isRegular.cof_eq]
    exact card_lt_of_mem_vonNeumann hκ hx
  · intro j
    exact (isSuccLimit_ord hκ).succ_lt (ZFSet.mem_vonNeumann.mp (hf _))

/-! ## The first-order language of set theory -/

/-- Relation symbols for the language of set theory: a single binary membership relation. -/
inductive memRel : ℕ → Type
  | mem : memRel 2
  deriving DecidableEq

/-- The first-order language of set theory: one binary relation symbol, for `∈`. -/
