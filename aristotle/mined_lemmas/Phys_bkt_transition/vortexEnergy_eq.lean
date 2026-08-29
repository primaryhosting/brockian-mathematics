import Mathlib

/-!
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
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

/-! ## The two–dimensional XY model -/

/-- Sites of the two-dimensional square lattice `ℤ²`. -/
abbrev Site : Type := ℤ × ℤ

/-- The XY-model Hamiltonian `H(θ) = -J ∑_{⟨xy⟩} cos (θ x - θ y)` for a finite collection
of nearest-neighbour bonds. -/

theorem vortexEnergy_eq (J L : ℝ) (hL : 0 < L) :
    vortexEnergy J L = Real.pi * J * Real.log L := by
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) L := by
    intro hmem
    rcases Set.mem_uIcc.mp hmem with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have h : ∀ r : ℝ, Real.pi * J / r = (Real.pi * J) * (1 / r) := by intro r; ring
  simp only [vortexEnergy, h]
  rw [intervalIntegral.integral_const_mul, integral_one_div h0, div_one]

/-- The entropy of a single vortex in a box of linear size `L`: its core can be placed in any
of the `L²` plaquettes, so `S = log (L²)`. -/
