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

lemma margB_copySys (b : ↥leftPartᶜ → Bool) : margB copySys leftPart b = 1 / 2 := by
  rw [margB, sum_left (fun a => jointProb copySys leftPart a b)]
  simp only [jointProb_copySys]
  cases hB : b default <;> norm_num

/-- The two-node "copy" system has effective information `log 2` across its bipartition;
in particular effective information as defined above is not identically zero, so the vanishing
of `Φ` for disconnected systems is not a triviality. -/
