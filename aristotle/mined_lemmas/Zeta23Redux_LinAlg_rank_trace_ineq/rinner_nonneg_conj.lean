/-
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Lean requires `import` to precede any module docstring, so the header is
repeated as a module docstring immediately after the import below.)
-/
import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Zeta23Redux.LinAlg

open Matrix

/-- Square complex matrices of size `Fin d`. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

variable {d : ℕ}

/-- The real part of the trace. -/

lemma rinner_nonneg_conj {A S : Mat d} (hA : A.PosSemidef) (hS : S.IsHermitian) :
    0 ≤ rinner A (S * S) := by
  have h : (Sᴴ * A * S).PosSemidef := hA.conjTranspose_mul_mul_same S
  have hnn := h.trace_nonneg
  rw [Complex.le_def] at hnn
  have h2 : Matrix.trace (A * (S * S)) = Matrix.trace (Sᴴ * A * S) := by
    calc Matrix.trace (A * (S * S)) = Matrix.trace ((A * S) * S) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (S * (A * S)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Sᴴ * A * S) := by rw [hS.eq, Matrix.mul_assoc]
  simpa [rinner, h2] using hnn.1

/-! ### Conjugated diagonal matrices -/

/-- `cdiag U f = U * diagonal f * Uᴴ`. -/
