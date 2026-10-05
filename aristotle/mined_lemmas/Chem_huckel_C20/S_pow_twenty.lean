import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset Polynomial

set_option maxHeartbeats 1000000

/-! ## Generalities on eigenvalues of matrices -/

/-- A scalar `μ` is an eigenvalue of `M` iff `M - μ • 1` is singular. -/

lemma S_pow_twenty : S ^ 20 = 1 := by
  rw [S_pow]; ext i j; simp [Matrix.one_apply, Fin.ofNat, eq_comm]

/-- The adjacency matrix of the cycle graph `C₂₀`, over `ℂ`. -/
