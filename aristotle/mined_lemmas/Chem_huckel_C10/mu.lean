/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Matrix
open Complex

namespace Chem

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₀`. -/

noncomputable def mu (k : Fin 10) : ℂ := ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 10) : ℝ) : ℂ)

/-- The matrix of eigenvectors: `F i k = (ζ^k)^i`. -/
