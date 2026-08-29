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

lemma AC_eq : AC = S + S ^ 19 := by
  rw [AC, S_pow]
  ext i j
  have hadj : (SimpleGraph.cycleGraph 20).Adj i j ↔ (j = i + 1 ∨ j = i + Fin.ofNat 20 19) := by
    revert i j; decide
  have hex : ¬(j = i + 1 ∧ j = i + Fin.ofNat 20 19) := by revert i j; decide
  simp only [SimpleGraph.adjMatrix_apply, Matrix.add_apply, Matrix.of_apply, S]
  by_cases h1 : j = i + 1 <;> by_cases h2 : j = i + Fin.ofNat 20 19 <;>
    simp [h1, h2, hadj] at * <;> tauto

/-! ## The eigenvectors -/

/-- The discrete Fourier vector `j ↦ w ^ (j k)`. -/
