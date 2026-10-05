/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
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

noncomputable section

open Polynomial

/-! ## Probabilists' Hermite polynomials over `ℝ` -/

/-- The `n`-th probabilists' Hermite polynomial, with real coefficients. -/

theorem hasDerivAt_hermiteGaussD (n : ℕ) {s : ℝ} (hs : s ≠ 0) (u : ℝ) :
    HasDerivAt (hermiteGaussD n s)
      ((u ^ 2 / (4 * s ^ 4) - ((n : ℝ) + 1 / 2) / s ^ 2) * hermiteGauss n s u) u := by
  have hv : HasDerivAt (fun t : ℝ => t / s) (1 / s) u := by
    simpa using (hasDerivAt_id u).div_const s
  have hHe : HasDerivAt (fun t : ℝ => He n (t / s)) (He' n (u / s) * (1 / s)) u := by
    simpa only [Function.comp_def] using (hasDerivAt_He n (u / s)).comp u hv
  have hHe' : HasDerivAt (fun t : ℝ => He' n (t / s)) (He'' n (u / s) * (1 / s)) u := by
    simpa only [Function.comp_def] using (hasDerivAt_He' n (u / s)).comp u hv
  have hq : HasDerivAt (fun t : ℝ => -(t / s) ^ 2 / 4) (-(2 * (u / s) ^ 1 * (1 / s)) / 4) u :=
    ((hv.pow 2).neg).div_const 4
  have hE : HasDerivAt (fun t : ℝ => Real.exp (-(t / s) ^ 2 / 4))
      (Real.exp (-(u / s) ^ 2 / 4) * (-(2 * (u / s) ^ 1 * (1 / s)) / 4)) u := hq.exp
  have h1 : HasDerivAt (fun t : ℝ => t / (2 * s ^ 2)) (1 / (2 * s ^ 2)) u := by
    simpa only [one_div] using (hasDerivAt_id u).div_const (2 * s ^ 2)
  have hlin : HasDerivAt (fun t : ℝ => t / (2 * s ^ 2) * He n (t / s))
      (1 / (2 * s ^ 2) * He n (u / s) + u / (2 * s ^ 2) * (He' n (u / s) * (1 / s))) u := h1.mul hHe
  have hfac : HasDerivAt (fun t : ℝ => He' n (t / s) / s - t / (2 * s ^ 2) * He n (t / s))
      (He'' n (u / s) * (1 / s) / s -
        (1 / (2 * s ^ 2) * He n (u / s) + u / (2 * s ^ 2) * (He' n (u / s) * (1 / s)))) u :=
    (hHe'.div_const s).sub hlin
  have hmul := hfac.mul hE
  unfold hermiteGauss hermiteGaussD
  convert hmul using 1
  rw [He_ode n (u / s)]
  field_simp
  ring

/-! ## The two-dimensional Landau problem (Landau gauge `A = (0, B x, 0)`) -/

/-- Partial derivative in the `x` variable. -/
