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

noncomputable def oracleAmp (Q : ℕ) (f : ℕ → β) (j : ℕ) (y : β) : ℂ :=
  if j < Q ∧ f j = y then ((Real.sqrt Q : ℝ) : ℂ)⁻¹ else 0

/-- Amplitude of `|m⟩|y⟩` after applying the quantum Fourier transform modulo `Q`
to the first register. -/
