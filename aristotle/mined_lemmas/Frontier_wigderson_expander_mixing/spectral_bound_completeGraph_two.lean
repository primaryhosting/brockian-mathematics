import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Frontier

section Aux

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Cauchy–Schwarz for finite sums, in absolute-value / square-root form. -/

lemma spectral_bound_completeGraph_two :
    ∀ v : Fin 2 → ℝ, ∑ i, v i = 0 →
      Real.sqrt (∑ i, (((⊤ : SimpleGraph (Fin 2)).adjMatrix ℝ).mulVec v i) ^ 2)
        ≤ 1 * Real.sqrt (∑ i, (v i) ^ 2) := by
  intro v _
  have h : ∀ i, ((⊤ : SimpleGraph (Fin 2)).adjMatrix ℝ).mulVec v i = v (1 - i) := by
    intro i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply, Fin.sum_univ_two]
  simp only [h, one_mul, Fin.sum_univ_two]
  norm_num [add_comm]

end Frontier

