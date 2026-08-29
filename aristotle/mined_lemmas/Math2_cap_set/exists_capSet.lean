import Mathlib
/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
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

set_option grind.warning false

namespace Math2

open Finset Asymptotics Filter

/-- The cap set number `capSetNumber n` is the largest cardinality of a subset of
`𝔽₃ⁿ = (Fin n → ZMod 3)` containing no nontrivial three-term arithmetic progression. -/

lemma exists_capSet (n : ℕ) :
    ∃ A : Finset (Fin n → ZMod 3), #A = capSetNumber n ∧
      ThreeAPFree (A : Set (Fin n → ZMod 3)) := by
  obtain ⟨A, -, hcard, hAP⟩ := addRothNumber_spec (Finset.univ : Finset (Fin n → ZMod 3))
  exact ⟨A, hcard, hAP⟩

/-- The number of points of `𝔽₃ⁿ`. -/
