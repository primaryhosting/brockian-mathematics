/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Real

/-- The adjacency matrix of the cycle graph `C₅`, on vertex set `Fin 5` with the
cyclic (mod 5) neighbour relation. In Hückel theory (with `α = 0`, `β = 1`) this is the
Hückel matrix of the cyclic π-system of `C₅`. -/

lemma eigvec_two : ∃ v : Fin 5 → ℝ, v ≠ 0 ∧ C5adj *ᵥ v = (2 : ℝ) • v := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro hc
    have := congrFun hc 0
    norm_num at this
  · funext i
    fin_cases i <;>
      simp [C5adj_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

/-- Any root `t` of `x² + x - 1` is an eigenvalue of the `C₅` adjacency matrix. -/
