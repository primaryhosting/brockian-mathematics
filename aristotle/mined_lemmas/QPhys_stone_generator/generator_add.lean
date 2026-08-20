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

theorem generator_add {x y : H} (hx : x ∈ domain U)
    (hy : y ∈ domain U) : generator U (x + y) = generator U x + generator U y := by
  have hxy : HasDerivAt (fun t : ℝ => U t (x + y))
      (Complex.I • generator U x + Complex.I • generator U y) 0 := by
    simpa using (hasDerivAt_of_mem_domain hx).add (hasDerivAt_of_mem_domain hy)
  rw [generator_eq hxy, smul_add, smul_smul, smul_smul]
  simp

omit [CompleteSpace H] in
