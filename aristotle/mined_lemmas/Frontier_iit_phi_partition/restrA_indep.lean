/-
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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

namespace Frontier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The restriction of a global state `x` to the part `A` of the system. -/

lemma restrA_indep (h : DisconnectedAt f A) (u : ↥A → Bool) (v : ↥Aᶜ → Bool) :
    restr A (f (joinState A u v)) = restr A (f (joinState A u (fun _ => false))) := by
  funext i
  simp only [restr]
  exact h.1 _ _ (fun j hj => by simp [joinState, hj]) i i.2

/-- Across a disconnected cut, the next state of `Aᶜ` is determined by the current state of
`Aᶜ`. -/
