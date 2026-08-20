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

noncomputable def margB (f : (V → Bool) → (V → Bool)) (A : Finset V) (b : ↥Aᶜ → Bool) : ℝ :=
  ∑ a : ↥A → Bool, jointProb f A a b

/-- The **effective information** across the bipartition `(A, Aᶜ)`: the Kullback-Leibler
divergence between the effect repertoire of the whole system and the product of the effect
repertoires of the two parts (i.e. the effect repertoire of the system whose connections
across the cut have been severed and replaced by independent noise). -/
