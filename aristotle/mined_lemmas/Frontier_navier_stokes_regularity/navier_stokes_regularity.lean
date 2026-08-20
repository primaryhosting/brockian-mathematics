import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
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

namespace Frontier

/-! ## Differential operators on `ℝ³` -/

/-- Three dimensional Euclidean space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th partial derivative of a (vector or scalar valued) field on `ℝ³`. -/

theorem navier_stokes_regularity :
    (∀ ν : ℝ, SolvableData ν (fun _ => 0)) ∧
    (∀ (ν : ℝ) (u₀ : E3 → E3), SolvableData ν u₀ →
        ∀ c : ℝ, 0 < c → SolvableData ν (fun x => c • u₀ (c • x))) ∧
    (∀ eps : ℝ, 0 < eps →
        (∀ ν : ℝ, 0 < ν → ∀ U : SchwartzMap E3 E3, (∀ x, divg (⇑U) x = 0) →
          (∫ x : E3, ‖U x‖ ^ 2) < eps → SolvableData ν (⇑U)) →
        NavierStokesGlobalRegularity) :=
  ⟨solvableData_zero, fun _ _ h _ hc => solvableData_scale h hc,
    navierStokesGlobalRegularity_of_small_energy⟩

end Frontier

