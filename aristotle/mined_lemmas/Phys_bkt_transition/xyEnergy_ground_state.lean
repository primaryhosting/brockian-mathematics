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

theorem xyEnergy_ground_state (J : ℝ) (hJ : 0 ≤ J) (bonds : Finset (Site × Site))
    (θ : Site → ℝ) : -J * bonds.card ≤ xyEnergy J bonds θ := by
  have h : ∑ b ∈ bonds, Real.cos (θ b.1 - θ b.2) ≤ (bonds.card : ℝ) := by
    calc ∑ b ∈ bonds, Real.cos (θ b.1 - θ b.2) ≤ ∑ _b ∈ bonds, (1 : ℝ) :=
          Finset.sum_le_sum (fun b _ => Real.cos_le_one _)
      _ = (bonds.card : ℝ) := by simp
  have := mul_le_mul_of_nonneg_left h hJ
  simp only [xyEnergy, neg_mul]
  linarith

/-! ## Quantised vorticity: the topological charge -/

/-- The representative of an angle difference in `(-π, π]`, i.e. the lattice "gradient"
used to define the vorticity. -/
