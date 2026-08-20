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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Statement: Erasing one bit dissipates at least kT ln 2 of heat (Landauer).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

namespace Phys

open Finset

/-- Gibbs/Shannon entropy `S(p) = -k ∑ᵢ pᵢ log pᵢ` of a probability distribution `p`
on a finite state space, measured with Boltzmann constant `k`
(the convention `0 * log 0 = 0` is automatic since `Real.log 0 = 0`). -/

noncomputable def entropy (k : ℝ) {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  -k * ∑ i, p i * Real.log (p i)

/-- The state of one unknown bit: the uniform distribution on two states. -/
