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

noncomputable def blochMO (k : Fin 3) : Fin 3 → ℂ :=
  fun j => Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) * (j : ℕ)) / 3)

/-- The Bloch vector `blochMO k` is nonzero. -/
