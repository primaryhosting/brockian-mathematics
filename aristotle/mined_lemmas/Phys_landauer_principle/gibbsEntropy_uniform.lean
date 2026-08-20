import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Statement: Erasing one bit dissipates at least kT ln 2 of heat (Landauer).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

/-- The Gibbs (Boltzmann–Shannon) entropy `S = -k ∑ᵢ pᵢ log pᵢ` of a probability
distribution `p` on a finite set of microstates, with Boltzmann constant `k`. -/

theorem gibbsEntropy_uniform {ι : Type*} [Fintype ι] [Nonempty ι] (k : ℝ) (p : ι → ℝ)
    (hp : ∀ i, p i = (Fintype.card ι : ℝ)⁻¹) :
    gibbsEntropy k p = k * Real.log (Fintype.card ι) := by
  have hne : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [gibbsEntropy, hp, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [Real.log_inv]
  field_simp

/-- A deterministic (point-mass) distribution has zero entropy. -/
