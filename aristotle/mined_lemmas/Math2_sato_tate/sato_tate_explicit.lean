/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open Filter Topology

/-! ## The Sato–Tate measure -/

/-- The density of the Sato–Tate measure `(2/π) sin²θ dθ` on `[0, π]`. -/

theorem sato_tate_explicit (W : WeierstrassCurve ℤ) (hST : SatoTateHolds W)
    {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi) :
    Tendsto (fun N : ℕ =>
        (((primesBelow N).filter (fun p => frobeniusAngle W p ∈ Set.Icc a b)).card : ℝ)
          / ((primesBelow N).card : ℝ))
      atTop (𝓝 (((b - Real.sin b * Real.cos b) - (a - Real.sin a * Real.cos a)) / Real.pi)) := by
  have h := sato_tate W hST h0 hab hb
  rwa [integral_satoTateDensity,
    show satoTateCDF b - satoTateCDF a
      = ((b - Real.sin b * Real.cos b) - (a - Real.sin a * Real.cos a)) / Real.pi by
        unfold satoTateCDF; ring] at h

end Math2

