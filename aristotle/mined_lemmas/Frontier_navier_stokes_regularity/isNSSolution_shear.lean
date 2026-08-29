/-
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped ContDiff

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

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/

theorem isNSSolution_shear (ν : ℝ) (phi : ℝ → (Fin 3 → ℝ) → ℝ)
    (hsmooth : ContDiff ℝ ∞ (fun q : ℝ × (Fin 3 → ℝ) => phi q.1 q.2))
    (hindep : ∀ t : ℝ, ∀ x : Fin 3 → ℝ, ∀ s : ℝ, phi t (Function.update x 0 s) = phi t x)
    (hheat : ∀ t : ℝ, 0 ≤ t → ∀ x : Fin 3 → ℝ,
      deriv (fun s : ℝ => phi s x) t = ν * lap (phi t) x) :
    IsNSSolution ν (fun t x => ![phi t x, 0, 0]) (fun _ _ => 0) := by
  have hp0 : ∀ (t : ℝ) (x : Fin 3 → ℝ), pderiv 0 (phi t) x = 0 :=
    fun t x => pderiv_eq_zero_of_indep 0 (phi t) x (hindep t x)
  refine ⟨?_, contDiff_const, ?_, ?_⟩
  · rw [contDiff_pi]
    intro i
    fin_cases i
    · simpa using hsmooth
    · simpa using contDiff_const
    · simpa using contDiff_const
  · intro t _ x
    simp [divergence, Fin.sum_univ_three, hp0, pderiv_zero]
  · intro t ht x i
    fin_cases i <;>
      simp [Fin.sum_univ_three, hp0, pderiv_zero, lap_zero, hheat t ht x]

/-! ## An explicit nontrivial global solution -/

/-- The explicit shear flow `u(t,x) = (e^{-ν t} sin x₂, 0, 0)`. -/
