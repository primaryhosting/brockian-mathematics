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

theorem eq_zero_of_inner_domain (hU : IsUnitaryGroup U) {w : H}
    (hw : ∀ x ∈ domain U, ⟪x, w⟫_ℂ = 0) : w = 0 := by
  have hcont : Continuous fun v : H => ⟪v, w⟫_ℂ := continuous_id.inner continuous_const
  have hall : (fun v : H => ⟪v, w⟫_ℂ) = fun _ : H => (0 : ℂ) :=
    Continuous.ext_on (dense_domain hU) hcont continuous_const hw
  have : ⟪w, w⟫_ℂ = 0 := congrFun hall w
  exact inner_self_eq_zero.mp this

