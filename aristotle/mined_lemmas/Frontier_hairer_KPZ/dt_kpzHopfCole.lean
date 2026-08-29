import Mathlib
/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands of a
file, and a module docstring `/-! ... -/` is not allowed before them.  The required header
comment is therefore placed immediately after the single `import Mathlib` line.
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

namespace Frontier

/-! ## Partial derivatives in the space–time variables

Throughout, a space–time function is a map `u : ℝ → ℝ → ℝ`, written `u t x`, with `t` the
time variable and `x` the space variable. -/

/-- Time derivative `∂_t u` of a space–time function `u : ℝ → ℝ → ℝ`. -/

theorem dt_kpzHopfCole {t : ℝ} (ht : 0 < t) (x : ℝ) :
    dt kpzHopfCole t x = x ^ 2 / (4 * t ^ 2) - 1 / (2 * t) := by
  have hne : (4 : ℝ) * t ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => -x ^ 2 / (4 * s)) (x ^ 2 / (4 * t ^ 2)) t := by
    have hd : HasDerivAt (fun s : ℝ => 4 * s) 4 t := by
      simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
    have := (hd.inv hne).const_mul (-x ^ 2)
    convert this using 1
    · funext s; ring
    · field_simp
      ring
  have h2 : HasDerivAt (fun s : ℝ => Real.log (4 * Real.pi * s) / 2) (1 / (2 * t)) t := by
    have hpi : (4 : ℝ) * Real.pi ≠ 0 := by positivity
    have hd : HasDerivAt (fun s : ℝ => 4 * Real.pi * s) (4 * Real.pi) t := by
      simpa using (hasDerivAt_id t).const_mul (4 * Real.pi)
    have hne' : 4 * Real.pi * t ≠ 0 := by positivity
    have hlog : HasDerivAt (fun s : ℝ => Real.log (4 * Real.pi * s))
        ((4 * Real.pi) / (4 * Real.pi * t)) t := hd.log hne'
    have := hlog.div_const 2
    convert this using 1
    field_simp
  have := h1.sub h2
  simpa [dt, kpzHopfCole] using this.deriv

/-- **Base case.** The Cole–Hopf logarithm of the Gaussian heat kernel,
`h t x = -x²/(4t) - log(4πt)/2`, is an explicit classical solution of the free KPZ equation
(`ξ = 0`) for positive times. -/
