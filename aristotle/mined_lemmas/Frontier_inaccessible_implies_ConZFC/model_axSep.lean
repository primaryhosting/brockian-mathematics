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

theorem model_axSep {n : ℕ} (φ : setLang.BoundedFormula (Empty ⊕ Fin n) 2) :
    VSet o ⊨ axSep φ := by
  rw [realize_axSep]
  intro p x
  refine ⟨⟨ZFSet.sep (fun z => ∃ h : z ∈ V_ o,
      φ.Realize (Sum.elim default p) ![x, ⟨z, h⟩]) (x : ZFSet),
    subset_mem_V x.2 ZFSet.sep_subset⟩, fun z => ?_⟩
  rw [memR_VSet, ZFSet.mem_sep]
  constructor
  · rintro ⟨hzx, _, hφ⟩
    exact ⟨hzx, hφ⟩
  · rintro ⟨hzx, hφ⟩
    exact ⟨hzx, z.2, hφ⟩

variable {κ : Cardinal.{u}}

