/-
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment; the same text is repeated as a module docstring below.)

import Mathlib

/-!
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Polynomial
open scoped Classical

set_option maxHeartbeats 1000000

namespace AbelRuffiniQuintic

open Function Polynomial Polynomial.Gal Ideal

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

variable (R : Type*) [CommRing R] (a b : ℕ)

/-- The quintic `X ^ 5 - a * X + b`, which for suitable `a, b` is irreducible over `ℚ`
with Galois group `S₅`. -/

theorem gal_quintic_mulEquiv_perm_fin_five :
    Nonempty (quintic.Gal ≃* Equiv.Perm (Fin 5)) := by
  have h_irred := irreducible_quintic_witness
  have e1 : (Phi ℚ 4 2).Gal ≃* Equiv.Perm ((Phi ℚ 4 2).rootSet ℂ) :=
    MulEquiv.ofBijective _ (gal_Phi 4 2 (by norm_num) h_irred)
  have hcard : Fintype.card ((Phi ℚ 4 2).rootSet ℂ) = 5 :=
    complex_roots_Phi 4 2 h_irred.separable
  exact ⟨quintic_eq_Phi ▸ e1.trans (Fintype.equivFinOfCardEq hcard).permCongrHom⟩

end AbelRuffiniQuintic

namespace Math

open Polynomial AbelRuffiniQuintic

/-- **Abel–Ruffini theorem in degree 5**: there is no general solution by radicals for
quintic equations.  Concretely, the rational quintic `X ^ 5 - 4 * X + 2` has degree `5`,
its Galois group is not solvable (it is the symmetric group `S₅`), and *none* of its five
complex roots can be expressed by radicals over `ℚ`. -/
