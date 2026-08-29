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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

/-- **Counting form of the Gibbs phase rule.**

With `C ≥ 1` components distributed over `P ≥ 1` phases, the intensive state of the
system is described by `2 + P * (C - 1)` variables (temperature, pressure, and `C - 1`
independent mole fractions in each phase), while equality of the chemical potential of
each component across all phases imposes `C * (P - 1)` conditions.  The difference is
`C - P + 2`. -/
theorem gibbs_variable_count (C P : ℕ) (hC : 1 ≤ C) (hP : 1 ≤ P) :
    ((2 + P * (C - 1) : ℕ) : ℤ) - ((C * (P - 1) : ℕ) : ℤ) = (C : ℤ) - (P : ℤ) + 2 := by
  obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
  obtain ⟨p, rfl⟩ : ∃ p, P = p + 1 := ⟨P - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

/-- The solution set of an inhomogeneous linear system `f x = b` is an affine subspace:
it is the coset `x₀ + ker f` through any particular solution `x₀`. -/
theorem solution_set_eq_coset {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ₗ[ℝ] W) (b : W) (x₀ : V) (hx₀ : f x₀ = b) :
    {x : V | f x = b} = (fun v => x₀ + v) '' (LinearMap.ker f : Set V) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, LinearMap.mem_ker]
  constructor
  · intro hx
    refine ⟨x - x₀, ?_, by abel⟩
    simp [map_sub, hx, hx₀]
  · rintro ⟨v, hv, rfl⟩
    simp [map_add, hv, hx₀]

/-- **Gibbs phase rule** as an affine-dimension count.

Model: `V` is the space of intensive state variables of a `C`-component, `P`-phase system,
of dimension `2 + P * (C - 1)` (temperature, pressure, and `C - 1` independent mole
fractions per phase).  The equilibrium conditions are encoded by a linear map
`f : V →ₗ[ℝ] W` into the space `W` of constraint values, of dimension `C * (P - 1)`
(equality of each component's chemical potential between consecutive phases); the
constraints are assumed independent, i.e. `f` is surjective.

Then, for every attainable constraint value `b`, the set of equilibrium states is a
nonempty affine subspace — a coset of `ker f` — whose dimension, the number of degrees
of freedom, is

`F = C - P + 2`. -/
theorem gibbs_phase_rule {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]
    (C P : ℕ) (hC : 1 ≤ C) (hP : 1 ≤ P) (f : V →ₗ[ℝ] W)
    (hV : Module.finrank ℝ V = 2 + P * (C - 1))
    (hW : Module.finrank ℝ W = C * (P - 1))
    (hf : Function.Surjective f) :
    (Module.finrank ℝ (LinearMap.ker f) : ℤ) = (C : ℤ) - (P : ℤ) + 2 ∧
      ∀ b : W, ∃ x₀ : V, f x₀ = b ∧
        {x : V | f x = b} = (fun v => x₀ + v) '' (LinearMap.ker f : Set V) := by
  have hrange : Module.finrank ℝ (LinearMap.range f) = Module.finrank ℝ W := by
    rw [LinearMap.range_eq_top.2 hf, _root_.finrank_top]
  have key := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hW, hV] at key
  constructor
  · obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
    obtain ⟨p, rfl⟩ : ∃ p, P = p + 1 := ⟨P - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at key
    ring_nf at key
    have h2 : Module.finrank ℝ (LinearMap.ker f) + p = c + 2 := by omega
    have h3 := congrArg (fun n : ℕ => (n : ℤ)) h2
    push_cast at h3 ⊢
    linarith
  · intro b
    obtain ⟨x₀, hx₀⟩ := hf b
    exact ⟨x₀, hx₀, solution_set_eq_coset f b x₀ hx₀⟩

end Chem

