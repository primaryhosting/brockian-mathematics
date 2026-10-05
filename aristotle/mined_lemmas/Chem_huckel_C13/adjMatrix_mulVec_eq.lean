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

lemma adjMatrix_mulVec_eq (v : Fin 13 → ℂ) :
    ((SimpleGraph.cycleGraph 13).adjMatrix ℂ).mulVec v = cycA v := by
  funext i
  rw [SimpleGraph.adjMatrix_mulVec_apply, cycA_apply,
    SimpleGraph.cycleGraph_neighborFinset (n := 11) (v := i),
    Finset.sum_pair (fin13_sub_one_ne i), fin13_sub_one i]
  ring

/-! ### The 13-th roots of unity -/

/-- `ζ = exp (2πi/13)`, a primitive 13-th root of unity. -/
