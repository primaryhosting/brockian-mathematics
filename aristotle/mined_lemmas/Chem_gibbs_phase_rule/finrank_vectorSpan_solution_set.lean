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

theorem finrank_vectorSpan_solution_set {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (hf : Function.Surjective f) (b : W) :
    {v : V | f v = b}.Nonempty ∧
      Module.finrank ℝ (vectorSpan ℝ {v : V | f v = b}) + Module.finrank ℝ W
        = Module.finrank ℝ V := by
  obtain ⟨hne, hspan⟩ := vectorSpan_solution_set f hf b
  refine ⟨hne, ?_⟩
  rw [hspan]
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.2 hf] at h
  simp only [finrank_top] at h
  omega

/-! ## The intensive state space of a `P`-phase, `C`-component system -/

/-- The space of intensive variables of a system with `C` components and `P` phases:
temperature, pressure, and the mole fraction of each component in each phase. -/
abbrev PhaseState (C P : ℕ) : Type := ℝ × ℝ × (Fin P → Fin C → ℝ)

/-- The normalization constraints: in each phase the mole fractions sum to `1`.
This linear map sends a state to the vector of per-phase sums of mole fractions. -/
