import Mathlib
/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
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

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Kato's adiabatic generator associated with a smooth family of spectral projections
`P` with derivative `P'`: `K(s) = [P'(s), P(s)] = P'(s)P(s) - P(s)P'(s)`. -/

lemma proj_of_pauli {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] (X Y : A) (c s : ℂ)
    (hX : X * X = 1) (hY : Y * Y = 1) (hXY : X * Y + Y * X = 0) (hcs : c ^ 2 + s ^ 2 = 1) :
    ((2:ℂ)⁻¹ • (1 + c • X + s • Y)) * ((2:ℂ)⁻¹ • (1 + c • X + s • Y))
      = (2:ℂ)⁻¹ • (1 + c • X + s • Y) := by
  have hyx : Y * X = - (X * Y) := by linear_combination (norm := module) hXY
  have hs2 : s ^ 2 = 1 - c ^ 2 := by linear_combination hcs
  simp only [smul_mul_assoc, mul_smul_comm, mul_add, add_mul, one_mul, mul_one, smul_smul,
    smul_add, hX, hY, hyx]
  match_scalars <;> ring_nf <;> rw [hs2] <;> ring

/-- The Kato generator of such a family of projections. -/
