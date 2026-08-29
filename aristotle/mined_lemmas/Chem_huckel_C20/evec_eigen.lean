/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix SimpleGraph

/-- A primitive 20-th root of unity. -/

lemma evec_eigen (k : Fin 20) :
    ((SimpleGraph.cycleGraph 20).adjMatrix ℂ).mulVec (evec k) = eval20 k • evec k := by
  funext i
  rw [adj_mulVec, evec_succ, evec_pred, Pi.smul_apply, smul_eq_mul, ← om_pow_add_om_pow k]
  ring

