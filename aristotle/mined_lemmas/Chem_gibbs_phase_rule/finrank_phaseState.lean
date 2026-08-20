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

theorem finrank_phaseState (C P : ℕ) :
    Module.finrank ℝ (PhaseState C P) = 2 + P * C := by
  show Module.finrank ℝ (ℝ × ℝ × (Fin P → Fin C → ℝ)) = 2 + P * C
  rw [Module.finrank_prod, Module.finrank_prod, finrank_matrix_space, Module.finrank_self]
  omega

