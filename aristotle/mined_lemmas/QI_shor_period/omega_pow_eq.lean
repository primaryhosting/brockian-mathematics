/-
The quantum period-finding subroutine: the state produced by the algorithm,
the measurement distribution of the first register, and the lower bound on the
probability of a "good" measurement outcome.
-/
import Mathlib
import RequestProject.Analysis

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 2000000

namespace QI

/-- The primitive `Q`-th root of unity `e^{2πi/Q}` used by the quantum Fourier transform. -/

theorem omega_pow_eq (Q n : ℕ) :
    omega Q ^ n = Complex.exp (((2 * Real.pi * (n / Q : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rw [omega_eq, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- Only the residue of the exponent modulo `Q` matters: if `n = sQ + d` then
`ω^n = e^{2πi d/Q}`. -/
