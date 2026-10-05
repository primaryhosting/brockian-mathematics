import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

noncomputable section

/-- A primitive 9-th root of unity. -/

lemma C9adj_mulVec (v : ZMod 9 → ℂ) (i : ZMod 9) :
    (C9adj *ᵥ v) i = v (i + 1) + v (i - 1) := by
  simp [Matrix.mulVec, dotProduct, C9adj_apply, add_mul, Finset.sum_add_distrib, ite_mul,
    Finset.sum_ite_eq']

/-! ### Diagonalisation -/

