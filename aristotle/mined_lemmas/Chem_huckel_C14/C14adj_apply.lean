/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Polynomial SimpleGraph

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₄`. -/

lemma C14adj_apply (i j : Fin 14) :
    C14adj i j = (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0) := by
  have hadj : ∀ u v : Fin 14, ((cycleGraph 14).Adj u v ↔ (v = u + 1 ∨ v = u - 1)) := by decide
  have hne : ∀ u : Fin 14, (u + 1 : Fin 14) ≠ u - 1 := by decide
  rw [C14adj, SimpleGraph.adjMatrix_apply]
  by_cases h1 : j = i + 1
  · have h2 : j ≠ i - 1 := by rw [h1]; exact hne i
    rw [if_pos ((hadj i j).2 (Or.inl h1)), if_pos h1, if_neg h2]
    norm_num
  · by_cases h2 : j = i - 1
    · rw [if_pos ((hadj i j).2 (Or.inr h2)), if_neg h1, if_pos h2]
      norm_num
    · rw [if_neg (fun hA => ((hadj i j).1 hA).elim h1 h2), if_neg h1, if_neg h2]
      norm_num

