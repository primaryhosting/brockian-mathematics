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

noncomputable def eig (k : Fin 10) : ℂ := 2 * Real.cos (2 * Real.pi * (k : ℕ) / 10)

/-- The discrete-Fourier (Vandermonde) matrix built from `zeta`. -/
