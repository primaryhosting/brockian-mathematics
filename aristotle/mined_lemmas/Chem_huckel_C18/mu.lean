import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean 4 requires `import` commands to occur at the very beginning of a file,
before any module docstring, hence the header comment above appears just after the import.
-/

open Complex Polynomial Matrix

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

noncomputable def mu (k : Fin 18) : ℂ := ((2 * Real.cos (2 * Real.pi * k / 18) : ℝ) : ℂ)

/-- The (complex) adjacency matrix of the cycle graph `C₁₈`. -/
