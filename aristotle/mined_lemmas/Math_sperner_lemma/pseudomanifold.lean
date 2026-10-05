import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

/-! ## Auxiliary counting lemmas -/

/-- Parity translated into `ZMod 2`. -/

lemma pseudomanifold : ∀ (J : Finset (Fin 2)) (τ : Finset (Fin 3)),
    τ ∈ cplx → τ.card + 1 = J.card → (∀ v ∈ τ, carrier v ⊆ J) →
    ((spernerCells carrier cplx J).filter (fun σ => τ ⊆ σ)).card
      = if τ.biUnion carrier = J then 2 else 1 := by decide

/-- Here the `2` branch of the pseudomanifold condition really occurs: the interior
vertex `1` is a face of both edges. -/
