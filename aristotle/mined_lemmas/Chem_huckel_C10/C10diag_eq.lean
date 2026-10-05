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

namespace Chem

open Matrix SimpleGraph Polynomial

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₀`.  This is the Hückel matrix of
cyclodecapentaene in units where the Coulomb integral `α` is `0` and the resonance integral
`β` is `1`. -/

lemma C10diag_eq :
    C10diag = Matrix.diagonal fun k : Fin 10 => zeta ^ (k : ℕ) + zeta ^ (10 - (k : ℕ)) := by
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  rw [zeta_pow_add_zeta_pow (k : ℕ) (le_of_lt k.isLt)]
  simp [huckelEigenvalue]

/-- Every vertex of `C₁₀` has exactly two neighbours. -/
