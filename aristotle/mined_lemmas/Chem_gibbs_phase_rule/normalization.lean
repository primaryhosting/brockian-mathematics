import Mathlib
/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
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

set_option grind.warning false

namespace Chem

/-! ## An affine dimension count for linear systems -/

/-- For a surjective linear map `f`, the solution set of `f v = b` is nonempty and its
direction (the vector span of the solution set) is exactly `ker f`. -/

def normalization (C P : ℕ) : PhaseState C P →ₗ[ℝ] (Fin P → ℝ) where
  toFun s j := ∑ i, s.2.2 j i
  map_add' := by intro s t; funext j; simp [Finset.sum_add_distrib]
  map_smul' := by intro c s; funext j; simp [Finset.mul_sum]

/-- The full constraint map: normalization of mole fractions in each phase together with the
`(P-1) * C` equalities of chemical potentials between phases (encoded by a linear map
`equil`, i.e. the linearization of the equilibrium conditions). -/
