/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Complex

/-- A primitive 16-th root of unity. -/

lemma sum_over_neighbors (i : Fin 16) (v : Fin 16 → ℂ) :
    ∑ j, C16adj i j * v j = v (i - 1) + v (i + 1) := by
  have hstep : ∀ j : Fin 16, C16adj i j * v j
      = if j ∈ ({i - 1, i + 1} : Finset (Fin 16)) then v j else 0 := by
    intro j
    by_cases h : j = i - 1 ∨ j = i + 1
    · simp [C16adj, SimpleGraph.adjMatrix_apply, (adjMatrix_apply_iff i j).mpr h, h]
    · have hnot : ¬ (SimpleGraph.cycleGraph 16).Adj i j := fun hA =>
        h ((adjMatrix_apply_iff i j).mp hA)
      simp [C16adj, SimpleGraph.adjMatrix_apply, hnot, Finset.mem_insert,
        not_or.mp h |>.1, not_or.mp h |>.2]
  rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_pair (sub_one_ne_add_one i)]

/-- The Fourier (Vandermonde/DFT) matrix conjugates the adjacency matrix of `C₁₆`
into the diagonal matrix of Hückel eigenvalues. -/
