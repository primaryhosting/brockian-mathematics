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

@[simp] lemma restr_compl_joinState (A : Finset V) (u : ↥A → Bool) (v : ↥Aᶜ → Bool) :
    restr Aᶜ (joinState A u v) = v := by
  funext i
  have hi : (i : V) ∉ A := Finset.mem_compl.mp i.2
  simp [restr, joinState, hi]

/-- Splitting a global state into the pair of its restrictions to `A` and to `Aᶜ`. -/
