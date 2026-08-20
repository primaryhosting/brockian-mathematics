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

theorem model_axPair (hlim : IsSuccLimit o) : VSet o ⊨ axPair := by
  rw [realize_axPair]
  intro a b
  refine ⟨⟨({(a : ZFSet), (b : ZFSet)} : ZFSet), pair_mem_V hlim a.2 b.2⟩, fun z => ?_⟩
  simp

