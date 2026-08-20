import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space `H`. -/
structure IsUnitaryGroup (U : ℝ → H →L[ℂ] H) : Prop where
  map_zero : U 0 = ContinuousLinearMap.id ℂ H
  map_add : ∀ s t, U (s + t) = (U s).comp (U t)
  inner_map : ∀ t x y, ⟪U t x, U t y⟫_ℂ = ⟪x, y⟫_ℂ
  cont : ∀ x, Continuous fun t => U t x

variable {U : ℝ → H →L[ℂ] H}

/-- The natural domain of the generator: those vectors for which `t ↦ U t x` is
differentiable at `0`. -/

theorem translate_mem_domain (hU : IsUnitaryGroup U) {x : H} (hx : x ∈ domain U) (t : ℝ) :
    U t x ∈ domain U ∧ generator U (U t x) = U t (generator U x) := by
  have h1 : HasDerivAt (fun s : ℝ => U (s + t) x) (U t (Complex.I • generator U x)) 0 :=
    HasDerivAt.comp_add_const (f := fun u : ℝ => U u x) 0 t (by simpa using hasDerivAt_all hU hx t)
  have key : ∀ s : ℝ, U (s + t) x = U s (U t x) := by
    intro s
    rw [← ContinuousLinearMap.comp_apply, ← hU.map_add]
  rw [funext key] at h1
  refine ⟨⟨_, h1⟩, ?_⟩
  rw [generator_eq h1, map_smul, smul_smul]
  simp

omit [CompleteSpace H] in
