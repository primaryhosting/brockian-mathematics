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

def spernerDoors (J : Finset (Fin (n + 1))) (i₀ : Fin (n + 1)) : Finset (Finset V) :=
  T.filter (fun τ => τ.card + 1 = J.card ∧ (∀ v ∈ τ, carrier v ⊆ J) ∧ τ.image c = J.erase i₀)

variable
  (hdown : ∀ σ ∈ T, ∀ τ ⊆ σ, τ ∈ T)
  (hT0 : (∅ : Finset V) ∈ T)
  (hpm : ∀ (J : Finset (Fin (n + 1))) (τ : Finset V), τ ∈ T → τ.card + 1 = J.card →
      (∀ v ∈ τ, carrier v ⊆ J) →
      ((spernerCells carrier T J).filter (fun σ => τ ⊆ σ)).card
        = if τ.biUnion carrier = J then 2 else 1)
  (hc : ∀ v, c v ∈ carrier v)

omit [DecidableEq V] in
include hc in
/-- Colours of a cell of `F J` lie in `J`. -/
