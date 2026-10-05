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

private lemma ofNat_succ (k : ℕ) : (Fin.ofNat 20 (k + 1) : Fin 20) = Fin.ofNat 20 k + 1 := by
  apply Fin.ext; simp [Fin.ofNat, Fin.add_def]

