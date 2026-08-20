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

lemma cdiag_add (U : Mat d) (f g : Fin d → ℝ) :
    cdiag U f + cdiag U g = cdiag U (fun i => f i + g i) := by
  have h : (Matrix.diagonal fun i => (((f i + g i : ℝ)) : ℂ))
      = Matrix.diagonal (fun i => ((f i : ℝ) : ℂ))
        + Matrix.diagonal (fun i => ((g i : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  simp only [cdiag, h, Matrix.mul_add, Matrix.add_mul]

