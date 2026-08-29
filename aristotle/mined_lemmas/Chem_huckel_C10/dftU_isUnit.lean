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

lemma dftU_isUnit : IsUnit dftU := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, dftU_eq_vandermonde]
  rw [Matrix.det_vandermonde_ne_zero_iff]
  intro i j hij
  exact Fin.ext (zeta_isPrimitiveRoot.pow_inj i.isLt j.isLt hij)

/-- The diagonal matrix of Hückel eigenvalues of `C₁₀`. -/
