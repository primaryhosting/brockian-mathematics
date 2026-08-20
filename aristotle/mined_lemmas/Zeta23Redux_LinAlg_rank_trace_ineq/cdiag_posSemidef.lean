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

lemma cdiag_posSemidef (hf : ∀ i, 0 ≤ f i) : (cdiag U f).PosSemidef := by
  have hD : (Matrix.diagonal (fun i => ((f i : ℝ) : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    simpa using hf i
  simpa [cdiag, Matrix.mul_assoc] using hD.conjTranspose_mul_mul_same Uᴴ

