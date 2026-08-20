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

theorem model_axExt : VSet o ⊨ axExt := by
  rw [realize_axExt]
  intro a b h
  refine Subtype.ext (ZFSet.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
  · exact (h ⟨z, mem_mem_V a.2 hz⟩).1 hz
  · exact (h ⟨z, mem_mem_V b.2 hz⟩).2 hz

