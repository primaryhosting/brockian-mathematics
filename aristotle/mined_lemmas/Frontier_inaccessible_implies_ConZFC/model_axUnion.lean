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

theorem model_axUnion : VSet o ⊨ axUnion := by
  rw [realize_axUnion]
  intro x
  refine ⟨⟨⋃₀ (x : ZFSet), sUnion_mem_V x.2⟩, fun w => ?_⟩
  constructor
  · intro hw
    obtain ⟨z, hz, hwz⟩ := ZFSet.mem_sUnion.1 hw
    exact ⟨⟨z, mem_mem_V x.2 hz⟩, hz, hwz⟩
  · rintro ⟨z, hz, hwz⟩
    exact ZFSet.mem_sUnion.2 ⟨(z : ZFSet), hz, hwz⟩

