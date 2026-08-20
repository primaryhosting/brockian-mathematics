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

lemma sum_fin2_first (F : Bool → ℝ) :
    ∑ x : Fin 2 → Bool, F (x 0) = 2 * F true + 2 * F false := by
  rw [← Equiv.sum_comp (piFinTwoEquiv (fun _ => Bool)).symm (fun x => F (x 0))]
  simp [Fintype.sum_prod_type]

