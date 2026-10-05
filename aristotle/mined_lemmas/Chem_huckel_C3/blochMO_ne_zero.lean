import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Polynomial

/-- Adjacency matrix of the cycle graph `C₃` (the Hückel matrix of cyclopropenyl,
in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`). -/

lemma blochMO_ne_zero (k : Fin 3) : blochMO k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [blochMO] at h0

/-- The Bloch vector `blochMO k` is an eigenvector of the `C₃` adjacency matrix
with eigenvalue `2 cos (2πk/3)`. -/
