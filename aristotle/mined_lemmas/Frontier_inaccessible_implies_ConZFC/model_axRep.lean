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

theorem model_axRep (hκ : κ.IsInaccessible) {n : ℕ}
    (φ : setLang.BoundedFormula (Empty ⊕ Fin n) 3) : VSet κ.ord ⊨ axRep φ := by
  rw [realize_axRep]
  intro p x hfun
  choose f hf huniq using fun z : ↥(x : ZFSet) =>
    hfun ⟨(z : ZFSet), mem_mem_V x.2 z.2⟩ z.2
  refine ⟨⟨ZFSet.range (fun z => ((f z : VSet κ.ord) : ZFSet)),
    range_mem_V hκ x.2 _ (fun z => (f z).2)⟩, ?_⟩
  intro z hz w hw
  have huw := huniq ⟨(z : ZFSet), hz⟩ w hw
  rw [memR_VSet, ZFSet.mem_range]
  exact ⟨⟨(z : ZFSet), hz⟩, by rw [← huw]⟩

