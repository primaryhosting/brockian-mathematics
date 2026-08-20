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

theorem vectorSpan_solution_set {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ₗ[ℝ] W) (hf : Function.Surjective f) (b : W) :
    {v : V | f v = b}.Nonempty ∧
      vectorSpan ℝ {v : V | f v = b} = LinearMap.ker f := by
  obtain ⟨v₀, hv₀⟩ := hf b
  refine ⟨⟨v₀, hv₀⟩, le_antisymm ?_ ?_⟩
  · rw [vectorSpan_def]
    apply Submodule.span_le.2
    rintro x ⟨p, hp, q, hq, rfl⟩
    simp only [Set.mem_setOf_eq] at hp hq
    simp [LinearMap.mem_ker, vsub_eq_sub, hp, hq]
  · intro w hw
    have hrw : w = (v₀ + w) -ᵥ v₀ := by simp
    rw [hrw]
    refine vsub_mem_vectorSpan ℝ ?_ hv₀
    simp only [Set.mem_setOf_eq, map_add, hv₀, LinearMap.mem_ker.1 hw, add_zero]

/-- **Key intermediate lemma (affine rank–nullity).**  If `f : V →ₗ[ℝ] W` is surjective and
`V` is finite dimensional, then for every `b` the affine solution set `{v | f v = b}` is
nonempty and its affine dimension is `finrank V - finrank W`. -/
