import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace Brockian

open Matrix

/-- The planar rotation matrix by angle `θ`. -/

noncomputable def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- Each diagonal entry of a real orthogonal matrix has absolute value at most `1`
(its columns are unit vectors). -/
