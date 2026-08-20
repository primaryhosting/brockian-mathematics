import Mathlib
/-!
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
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

namespace QC

section CStar

variable {𝔄 : Type*} [NormedRing 𝔄] [StarRing 𝔄] [CStarRing 𝔄]

/-- In a C⋆-ring the unit has norm at most one (it is `0` or `1`). -/

theorem chsh_tsirelson {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A₀ A₁ B₀ B₁ : H →L[ℂ] H) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 2 * Real.sqrt 2 :=
  chsh_tsirelson_cstar A₀ A₁ B₀ B₁ T

end QC

