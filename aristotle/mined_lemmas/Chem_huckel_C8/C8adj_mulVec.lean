/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₈`, indexed by `ZMod 8`
(vertex `i` is adjacent to `i + 1` and `i - 1`), with complex entries. -/

lemma C8adj_mulVec (v : ZMod 8 → ℂ) (j : ZMod 8) :
    C8adj.mulVec v j = v (j + 1) + v (j - 1) := by
  have hrw : ∀ i : ZMod 8, (if i = j + 1 ∨ i = j - 1 then (1 : ℂ) else 0) * v i
      = if i ∈ ({j + 1, j - 1} : Finset (ZMod 8)) then v i else 0 := by
    intro i
    by_cases h : i = j + 1 ∨ i = j - 1 <;> simp [h, Finset.mem_insert]
  simp only [Matrix.mulVec, dotProduct, C8adj, hrw]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair (succ_ne_pred j)]

/-- A primitive 8th root of unity. -/
