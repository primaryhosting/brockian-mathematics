import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order

/-! ## The first-order language of set theory -/

/-- The relation symbols of the language of set theory: a single binary symbol `∈`. -/
inductive memRelSym : ℕ → Type
  | mem : memRelSym 2

/-- The first-order language of set theory: no function symbols, one binary relation `∈`. -/

theorem range_mem_V (hκ : κ.IsInaccessible) {x : ZFSet.{u}} (hx : x ∈ V_ κ.ord)
    (f : ↥x → ZFSet.{u}) (hf : ∀ i, f i ∈ V_ κ.ord) : ZFSet.range f ∈ V_ κ.ord := by
  rw [mem_vonNeumann, rank_range]
  rw [← Equiv.iSup_comp (α := Ordinal.{u}) (g := fun i : ↥x => succ (rank (f i)))
    (equivShrink.{u} ↥x).symm]
  refine Cardinal.iSup_lt_ord_lift_of_isRegular hκ.isRegular ?_ ?_
  · simpa [ZFSet.card] using card_lt_of_mem_V hκ hx
  · intro i
    exact (isSuccLimit_ord hκ.aleph0_lt.le).succ_lt (rank_lt_of_mem_V (hf _))

end Inaccessible

/-! ## The model -/

section Model

variable {o : Ordinal.{u}}

/-- The universe of the model: the elements of `V_ o`. -/
