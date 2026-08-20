import Mathlib
/-!
# Le Chatelier Sign
Category: Chemistry
Target: Chem.leChatelier_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- **van 't Hoff / Le Chatelier sign law.**

If the equilibrium constant `K` of a reaction is positive on the physical temperature range
`T > 0` and satisfies the van 't Hoff equation

  `dK/dT = K(T) * ΔH / (R * T ^ 2)`,

equivalently `d (log K) / dT = ΔH / (R T²)`, then for an *exothermic* reaction (`ΔH < 0`)
the function `K` is strictly decreasing in `T`.

The key Mathlib ingredient is `strictAntiOn_of_deriv_neg`. -/

theorem leChatelier_sign_arrhenius (R ΔH A : ℝ) (hR : 0 < R) (hH : ΔH < 0) (hA : 0 < A) :
    StrictAntiOn (fun T : ℝ => A * Real.exp (-ΔH / (R * T))) (Set.Ioi (0 : ℝ)) := by
  set K : ℝ → ℝ := fun T : ℝ => A * Real.exp (-ΔH / (R * T)) with hKdef
  refine leChatelier_sign R ΔH hR hH K (fun T _ => by positivity) ?_
  intro T hT
  have hT0 : (0 : ℝ) < T := hT
  have hRT : R * T ≠ 0 := by positivity
  have hinner : HasDerivAt (fun T : ℝ => -ΔH / (R * T)) (ΔH / (R * T ^ 2)) T := by
    have h1 : HasDerivAt (fun T : ℝ => R * T) R T := by
      simpa using (hasDerivAt_id T).const_mul R
    have h2 := HasDerivAt.div (hasDerivAt_const T (-ΔH)) h1 hRT
    simp only [zero_mul, zero_sub] at h2
    convert h2 using 1
    field_simp
  have := (Real.hasDerivAt_exp _).comp T hinner
  have h3 := this.const_mul A
  convert h3 using 1
  simp [hKdef]
  ring

end Chem

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

