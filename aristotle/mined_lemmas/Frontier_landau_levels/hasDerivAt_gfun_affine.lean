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

set_option grind.warning false

namespace Frontier

open Polynomial

/-! ## Physicists' Hermite polynomials -/

/-- The physicists' Hermite polynomials, defined by `H₀ = 1` and
`H_{n+1} = 2X H_n - H_n'`. -/

theorem hasDerivAt_gfun_affine (p : ℝ[X]) (c d t : ℝ) :
    HasDerivAt (fun s : ℝ => gfun p (c * (s - d))) (c * gfun (derivative p - X * p) (c * (t - d))) t := by
  have h : HasDerivAt (fun s : ℝ => c * (s - d)) c t := by
    simpa using ((hasDerivAt_id t).sub_const d).const_mul c
  simpa [mul_comm] using (hasDerivAt_gfun p (c * (t - d))).comp t h

/-- The `n`-th harmonic oscillator eigenfunction (unnormalised): `H_n(t) e^{-t²/2}`. -/
