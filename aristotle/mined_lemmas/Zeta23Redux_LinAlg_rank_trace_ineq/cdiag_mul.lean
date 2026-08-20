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

lemma cdiag_mul (hU : Uᴴ * U = 1) (f g : Fin d → ℝ) :
    cdiag U f * cdiag U g = cdiag U (fun i => f i * g i) := by
  simp only [cdiag, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal fun i => ((f i : ℝ) : ℂ)), Matrix.diagonal_mul_diagonal]
  simp

