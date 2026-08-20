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

lemma EI_eq_zero_of_factorizes
    (h : ∀ a b, jointProb f A a b = margA f A a * margB f A b) : EI f A = 0 := by
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  rw [h a b]
  rcases eq_or_ne (margA f A a * margB f A b) 0 with h0 | h0
  · rw [h0]; simp
  · rw [div_self h0, Real.log_one, mul_zero]

end Lemmas

section Disconnected

variable (f : (V → Bool) → (V → Bool)) (A : Finset V)

