import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Polynomial

namespace Chem

/-- A primitive 9th root of unity. -/

theorem adj_sum (j : Fin 9) (f : Fin 9 → ℂ) :
    ∑ l : Fin 9, ((SimpleGraph.cycleGraph 9).adjMatrix ℂ) j l * f l = f (j + 1) + f (j - 1) := by
  have hterm : ∀ l : Fin 9, ((SimpleGraph.cycleGraph 9).adjMatrix ℂ) j l * f l
      = (if l = j + 1 then f l else 0) + (if l = j - 1 then f l else 0) := by
    intro l
    rw [SimpleGraph.adjMatrix_apply]
    by_cases h1 : l = j + 1
    · rw [if_pos ((adj_iff j l).2 (Or.inl h1)), if_pos h1,
        if_neg (by rw [h1]; exact sub_one_ne_add_one j), one_mul, add_zero]
    · by_cases h2 : l = j - 1
      · rw [if_pos ((adj_iff j l).2 (Or.inr h2)), if_pos h2, if_neg h1, one_mul, zero_add]
      · rw [if_neg (fun h => ((adj_iff j l).1 h).elim h1 h2), if_neg h1, if_neg h2, zero_mul,
          add_zero]
  rw [Finset.sum_congr rfl (fun l _ => hterm l), Finset.sum_add_distrib]
  simp

