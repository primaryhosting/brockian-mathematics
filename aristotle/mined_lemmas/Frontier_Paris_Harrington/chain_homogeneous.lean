import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- A finite set `Y` of positive integers is *relatively large* when its least element is at
most its cardinality. -/

lemma chain_homogeneous {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (t : ℕ) :
    ∀ s ⊆ chain n c t, s.card = n → c s = G c n ∅ := by
  intro s hs hcard
  have := chain_G n c t s hs (le_of_eq hcard)
  rw [hcard] at this
  simpa [G] using this

end PH

open Filter PH

/-- **Infinite Ramsey theorem** (ultrafilter proof), packaged as an increasing chain of finite
homogeneous sets of positive integers with cardinalities `0, 1, 2, …`. -/
