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

theorem exists_nondegenerate_single_phase (C : ℕ) (hC : 1 ≤ C) :
    ∃ equil : PhaseState C 1 →ₗ[ℝ] (Fin (1 - 1) → Fin C → ℝ),
      Function.Surjective (constraints C 1 equil) := by
  refine ⟨0, ?_⟩
  rintro ⟨a, b⟩
  refine ⟨(0, 0, fun j i => if i = ⟨0, hC⟩ then a j else 0), ?_⟩
  have hb : b = 0 := by funext k; exact absurd k.2 (by omega)
  simp [constraints, normalization, hb, LinearMap.prod_apply, Finset.sum_ite_eq']

end Chem

