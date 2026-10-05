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

theorem omega_pow_int (Q n : ℕ) (s d : ℤ) (h : (n : ℤ) = s * Q + d) (hQ : 0 < Q) :
    omega Q ^ n = Complex.exp (((2 * Real.pi * (d / Q : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rw [omega_pow_eq]
  have hQc : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  have hn : (n : ℝ) = s * Q + d := by exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
  have key : ((2 * Real.pi * ((n : ℝ) / Q) : ℝ) : ℂ) * Complex.I
      = ((2 * Real.pi * ((d : ℝ) / Q) : ℝ) : ℂ) * Complex.I
        + (s : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hn]; push_cast; field_simp; ring
  rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

variable {β : Type*} [DecidableEq β]

/-- Amplitude of the computational basis state `|j⟩|y⟩` in the state
`Q^{-1/2} ∑_{j < Q} |j⟩|f j⟩` obtained by querying the oracle for `f`
(for Shor's algorithm `f j = a^j mod N`) on a uniform superposition. -/
