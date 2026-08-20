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

noncomputable def A : Matrix (Fin 18) (Fin 18) ℂ := (SimpleGraph.cycleGraph 18).adjMatrix ℂ

/-- The matrix of characters, `P i j = ζ ^ (i * j)`; a Vandermonde matrix. -/
