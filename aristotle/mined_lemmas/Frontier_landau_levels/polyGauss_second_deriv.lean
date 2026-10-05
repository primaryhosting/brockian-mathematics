/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the header above is a plain block
-- comment; the same text is repeated below as the module docstring.)

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

open Polynomial

/-! ### Hermite polynomials: the Hermite differential equation

Mathlib provides `Polynomial.hermite : ℕ → ℤ[X]` (the *probabilists'* Hermite polynomials)
together with `Polynomial.hermite_succ`, but not the Hermite ODE, which we derive here. -/

/-- The Hermite differential equation `He_n'' = X * He_n' - n * He_n`. -/

theorem polyGauss_second_deriv (q : ℝ[X]) (c a b x0 : ℝ) (ha : a ≠ 0) (hab : a ^ 2 = 4 * b)
    (hq : derivative (derivative q) = X * derivative q - C c * q) (x : ℝ) :
    deriv (deriv (polyGauss q a b x0)) x
      = (4 * b ^ 2 * (x - x0) ^ 2 - 2 * b * (2 * c + 1)) * polyGauss q a b x0 x := by
  rw [deriv_polyGauss q a b x0 ha]
  set R : ℝ[X] := C a * derivative q - C (2 * b / a) * (X * q) with hR
  rw [(hasDerivAt_polyGauss R a b x0 x).deriv]
  have hev : (derivative (derivative q)).eval (a * (x - x0))
      = (a * (x - x0)) * (derivative q).eval (a * (x - x0)) - c * q.eval (a * (x - x0)) := by
    rw [hq]; simp
  have hdR : derivative R
      = C a * derivative (derivative q) - C (2 * b / a) * (q + X * derivative q) := by
    simp [hR, derivative_mul]
  rw [hdR]
  simp only [polyGauss, eval_sub, eval_add, eval_mul, eval_C, eval_X, hR]
  rw [hev]
  have hb : b = a ^ 2 / 4 := by linarith
  subst hb
  field_simp
  ring

/-! ### The one-dimensional harmonic oscillator -/

/-- The oscillator eigenfunction written in the normalized `polyGauss` shape. -/
