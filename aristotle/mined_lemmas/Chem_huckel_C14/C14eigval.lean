/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Polynomial SimpleGraph

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₄`. -/

noncomputable def C14eigval (k : Fin 14) : ℂ :=
  2 * (Real.cos (2 * Real.pi * k.val / 14) : ℝ)

/-- The `k`-th eigenvector of the adjacency matrix of `C₁₄`. -/
