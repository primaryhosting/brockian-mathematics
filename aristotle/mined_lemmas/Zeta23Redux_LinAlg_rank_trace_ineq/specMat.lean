import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators ComplexOrder

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ}

/-- The real part of the trace of a matrix. -/

noncomputable def specMat (hA : A.IsHermitian) (f : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun i => (f i : ℂ)) *
    (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ

