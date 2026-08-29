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

noncomputable def F : Matrix (Fin 10) (Fin 10) ℂ := Matrix.of fun i k => (zk k) ^ (i : ℕ)

