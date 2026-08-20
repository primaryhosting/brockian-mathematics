/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Note: Lean requires `import` to precede any module docstring `/-! ... -/`,
so this header is a plain block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix Polynomial

/-- A primitive 10-th root of unity. -/

noncomputable def Pmat : Matrix (Fin 10) (Fin 10) ℂ :=
  Matrix.vandermonde (fun i : Fin 10 => zeta ^ (i : ℕ))

/-- The adjacency matrix of the cycle graph `C₁₀`, over `ℂ`. -/
