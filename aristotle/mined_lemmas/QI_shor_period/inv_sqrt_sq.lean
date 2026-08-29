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

theorem inv_sqrt_sq (Q : ℕ) :
    ((Real.sqrt Q : ℝ) : ℂ)⁻¹ * ((Real.sqrt Q : ℝ) : ℂ)⁻¹ = (Q : ℂ)⁻¹ := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (Nat.cast_nonneg Q)]
  push_cast
  ring

