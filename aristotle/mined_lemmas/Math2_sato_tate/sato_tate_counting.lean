import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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

namespace Math2

open Filter Topology Set Polynomial

/-- The Sato–Tate density `(2/π) sin²θ` on the interval `[0, π]`. -/

theorem sato_tate_counting (a : ℕ → ℤ)
    (hW : ∀ m : ℕ, 1 ≤ m →
      Tendsto (fun N => primeAvg (frobeniusAngle a) (weyl m) N) atTop (𝓝 0))
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ π) :
    Tendsto (fun N => angleProportion (frobeniusAngle a) α β N) atTop
      (𝓝 (∫ t in α..β, stDensity t)) :=
  satoTate_proportion_tendsto
    ((satoTate_iff_weyl_tendsto_zero _
      fun _ => ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩).mpr hW) hα hαβ hβ

end Math2

