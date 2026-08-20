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

theorem model_axPow (hlim : IsSuccLimit o) : VSet o ⊨ axPow := by
  rw [realize_axPow]
  intro x
  refine ⟨⟨powerset (x : ZFSet), powerset_mem_V hlim x.2⟩, fun z => ?_⟩
  constructor
  · intro hz w hw
    exact ZFSet.mem_powerset.1 hz hw
  · intro h
    exact ZFSet.mem_powerset.2 fun w hw => h ⟨w, mem_mem_V z.2 hw⟩ hw

