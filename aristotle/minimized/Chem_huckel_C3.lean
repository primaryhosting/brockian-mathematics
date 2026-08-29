/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Real Matrix

/-- Adjacency matrix of the cycle graph `C₃` (the Hückel matrix of cyclopropenyl in
units where `α = 0`, `β = 1`): every pair of distinct vertices is adjacent. -/

def C3adj : Matrix (Fin 3) (Fin 3) ℝ := fun i j => if i = j then 0 else 1

/-- The Hückel eigenvalues of the cyclopropenyl ring `C₃`: a real number `μ` is an
eigenvalue of the adjacency matrix of `C₃` (i.e. `det (A - μ • 1) = 0`) if and only if
`μ = 2 cos (2πk/3)` for some `k ∈ {0, 1, 2}`. -/
