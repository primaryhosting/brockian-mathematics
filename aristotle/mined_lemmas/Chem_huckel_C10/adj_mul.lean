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

The adjacency eigenvalues of the cycle graph `C₁₀` are `2 cos (2πk/10)`, `k = 0, …, 9`:
the characteristic polynomial of the adjacency matrix of `SimpleGraph.cycleGraph 10`
factors as `∏ k, (X - 2 cos (2πk/10))`.
-/

namespace Chem

open Polynomial Matrix

/-! ### Arithmetic in `Fin 10`

`Fin 10` carries the modular addition and multiplication of `ZMod 10`, but Mathlib does not
register a `CommRing` instance on it, so `ring` is unavailable; the few needed ring identities
are checked by `decide`. -/

set_option maxRecDepth 10000 in

lemma adj_mul (M : Matrix (Fin 10) (Fin 10) ℂ) (i k : Fin 10) :
    (((SimpleGraph.cycleGraph 10).adjMatrix ℂ) * M) i k = M (i + 1) k + M (i - 1) k := by
  have hne : ∀ i : Fin 10, (i - 1 : Fin 10) ≠ i + 1 := by decide +revert
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Fin 10, ((SimpleGraph.cycleGraph 10).adjMatrix ℂ) i j * M j k
      = (if j = i + 1 then M j k else 0) + (if j = i - 1 then M j k else 0) := by
    intro j
    rw [SimpleGraph.adjMatrix_apply]
    simp only [cycleGraph_ten_adj]
    by_cases h1 : j = i + 1
    · have h2 : j ≠ i - 1 := by rw [h1]; exact (hne i).symm
      simp [h1, (hne i).symm]
    · by_cases h2 : j = i - 1
      · simp [h2, hne i]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib]
  simp

