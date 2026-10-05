/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Finset

namespace Chem

/-! ### The cyclic shift operator -/

/-- The cyclic shift endomorphism of `Fin 13 → ℂ`, `f ↦ (i ↦ f (i + 1))`. -/

lemma qpoly_comp_eq :
    qpoly.comp (X + X ^ 12) =
      ∏ w ∈ nthRootsFinset 13 (1 : ℂ), ((X + X ^ 12) - C (w + w⁻¹)) := by
  rw [qpoly, Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun w _ => ?_
  simp

