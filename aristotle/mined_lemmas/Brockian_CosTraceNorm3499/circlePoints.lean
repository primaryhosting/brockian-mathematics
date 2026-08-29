import Mathlib

/-!
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Matrix
open scoped ComplexOrder MatrixOrder

/-- The trace norm (Schatten 1-norm) of a complex square matrix:
the trace of the positive square root of `Aᴴ * A`. -/

noncomputable def circlePoints (n : ℕ) (θ : Fin n → ℝ) : Matrix (Fin n) (Fin 2) ℂ :=
  Matrix.of fun i k => if k = 0 then ((Real.cos (θ i) : ℝ) : ℂ) else ((Real.sin (θ i) : ℝ) : ℂ)

/-- The cosine Gram matrix is a genuine Gram matrix: `C = M * Mᴴ`. -/
