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

noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 10)

/-- The Hückel (adjacency) eigenvalues of the cycle `C₁₀`. -/
