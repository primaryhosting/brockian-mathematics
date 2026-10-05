import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix SimpleGraph Finset

/-- The adjacency matrix of the cycle graph `C₁₃` (the Hückel matrix of the
`C₁₃` carbon ring, in units where `α = 0` and `β = 1`). -/

noncomputable def vec (k : Fin 13) : Fin 13 → ℂ := fun j => zeta k ^ (j : ℕ)

/-- The `k`-th Hückel eigenvalue, `2 cos (2πk/13)`. -/
