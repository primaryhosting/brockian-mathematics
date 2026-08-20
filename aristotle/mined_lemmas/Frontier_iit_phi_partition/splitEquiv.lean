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

def splitEquiv (A : Finset V) : ((↥A → Bool) × (↥Aᶜ → Bool)) ≃ (V → Bool) where
  toFun uv := joinState A uv.1 uv.2
  invFun x := (restr A x, restr Aᶜ x)
  left_inv uv := by ext <;> simp
  right_inv x := by
    funext i
    by_cases h : i ∈ A <;> simp [joinState, restr, h]

/-- The probability, under a uniform ("maximum-entropy") perturbation of the current state,
that the next state of the system restricted to `A` is `a` and restricted to `Aᶜ` is `b`.
This is the *effect repertoire* of the deterministic transition function `f`. -/
