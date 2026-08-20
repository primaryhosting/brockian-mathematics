/-
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

open MeasureTheory Set Real

namespace Brockian
namespace DilationGenerator

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The substitution operator `U : (U f)(t) = e^{t/2} · f(eᵗ)`, at the level of functions. -/

theorem logSubSymm_congr_ae {h k : ℝ → F} (hhk : h =ᵐ[volume] k) :
    logSubSymm h =ᵐ[volume.restrict (Ioi (0 : ℝ))] logSubSymm k := by
  filter_upwards [quasiMeasurePreserving_log.ae_eq_comp hhk] with x hx
  simp only [logSubSymm]
  rw [show h (Real.log x) = (h ∘ Real.log) x from rfl, hx]
  rfl

variable (F)
variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 F] [IsBoundedSMul 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The unitary `U : L²(0, ∞) ≃ L²(ℝ)` induced by the substitution `x = eᵗ`,
`(U f)(t) = e^{t/2} · f(eᵗ)`, with inverse `(U⁻¹ h)(x) = x^{-1/2} · h(log x)`. -/
