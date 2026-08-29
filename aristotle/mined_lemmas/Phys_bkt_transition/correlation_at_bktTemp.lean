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

theorem correlation_at_bktTemp {J : ℝ} (hJ : 0 < J) (r : ℝ) :
    correlation J (bktTemp J) r = r ^ (-(1 / 4) : ℝ) := by
  rw [correlation, spinWaveExponent_at_bktTemp hJ]

/-- The BKT correlation length above the transition, `ξ(T) = exp (b / √(T - T_c))`: instead of
a power law it has an *essential* singularity at `T_c`. -/
