import Mathlib
/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Chem

open Complex Finset Matrix

/-- A primitive 7-th root of unity. -/

lemma adj_mulVec_evec (k : Fin 7) :
    (SimpleGraph.cycleGraph 7).adjMatrix ℂ *ᵥ (evec k) = (lam k : ℂ) • evec k := by
  funext i
  rw [adjMatrix_cycleGraph_mulVec]
  simp only [evec, Pi.smul_apply, smul_eq_mul]
  rw [← ee_add_ee_neg k]
  have h1 : (i - 1) * k = i * k + (-k) := by decide +revert
  have h2 : (i + 1) * k = i * k + k := by decide +revert
  rw [h1, h2, ee_add, ee_add]
  ring

