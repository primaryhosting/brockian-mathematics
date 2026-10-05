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

private theorem tendsto_inv_sqrt {b : ℝ} (hb : 0 < b) :
    Filter.Tendsto (fun u : ℝ => b / Real.sqrt u) (nhdsWithin 0 (Set.Ioi 0))
      Filter.atTop := by
  have hsqrt : Filter.Tendsto (fun u : ℝ => Real.sqrt u) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Filter.Tendsto (fun u : ℝ => Real.sqrt u) (nhds 0) (nhds (Real.sqrt 0)) :=
        (Real.continuous_sqrt).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      simpa using Real.sqrt_pos.2 hu
  have hinv : Filter.Tendsto (fun v : ℝ => b / v) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Filter.Tendsto.const_mul_atTop hb tendsto_inv_nhdsGT_zero)
  exact hinv.comp hsqrt

