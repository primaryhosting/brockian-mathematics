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

lemma sum_funUnique {ι : Type*} [Fintype ι] [DecidableEq ι] [Unique ι] (g : (ι → Bool) → ℝ) :
    ∑ h : ι → Bool, g h = g (fun _ => true) + g (fun _ => false) := by
  rw [← Equiv.sum_comp (Equiv.funUnique ι Bool).symm g, Fintype.sum_bool]
  rfl

