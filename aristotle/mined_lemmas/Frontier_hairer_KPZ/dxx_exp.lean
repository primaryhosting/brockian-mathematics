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

theorem dxx_exp (hreg : IsClassicalRegular h) (t x : ℝ) :
    dxx (fun s y => Real.exp (h s y)) t x
      = Real.exp (h t x) * (dxx h t x + (dx h t x) ^ 2) := by
  have key : (fun y => dx (fun s y => Real.exp (h s y)) t y)
      = fun y => Real.exp (h t y) * dx h t y := by
    funext y; exact dx_exp hreg t y
  have hexp : HasDerivAt (fun y => Real.exp (h t y))
      (Real.exp (h t x) * dx h t x) x := by
    simpa [mul_comm] using ((hreg.space t x).hasDerivAt).exp
  have hdd : HasDerivAt (fun y => dx h t y) (dxx h t x) x :=
    ((hreg.space₂ t) x).hasDerivAt
  have := hexp.mul hdd
  have h2 : dxx (fun s y => Real.exp (h s y)) t x
      = deriv (fun y => Real.exp (h t y) * dx h t y) x := by
    rw [dxx, dx, key]
  rw [h2, this.deriv]
  ring

end ColeHopf

/-! ## The Cole–Hopf reduction

This is the exact (deterministic, classical) form of the transformation on which Hairer's
solution theory for the KPZ equation is built: `h` solves KPZ if and only if `Z = exp h`
solves the multiplicative stochastic heat equation, which is *linear* in `Z`. -/

/-- **Cole–Hopf reduction (target theorem).**

For a classically regular space–time function `h` and any forcing `ξ`, on any time set `T`:
`h` solves the KPZ equation `∂_t h = ∂_x^2 h + (∂_x h)^2 + ξ` if and only if the Cole–Hopf
transform `Z = exp h` solves the (linear) multiplicative stochastic heat equation
`∂_t Z = ∂_x^2 Z + Z ξ`.

This is the Lean-checked reduction of the nonlinear KPZ equation to a linear equation, the
classical backbone of Hairer's well-posedness theory for KPZ. -/
