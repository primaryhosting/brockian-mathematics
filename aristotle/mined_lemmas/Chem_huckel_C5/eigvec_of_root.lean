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

lemma eigvec_of_root (t : ℝ) (ht : t ^ 2 + t - 1 = 0) :
    ∃ v : Fin 5 → ℝ, v ≠ 0 ∧ C5adj *ᵥ v = t • v := by
  refine ⟨![1, t / 2, -(t + 1) / 2, -(t + 1) / 2, t / 2], ?_, ?_⟩
  · intro hc
    have := congrFun hc 0
    norm_num at this
  · funext i
    fin_cases i <;>
      simp [C5adj_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> nlinarith [ht]

/-- The Hückel eigenvalue problem for the cycle `C₅`: a real number `μ` is an eigenvalue of the
adjacency matrix of `C₅` if and only if `μ = 2 cos(2πk/5)` for some `k ∈ {0, 1, 2, 3, 4}`. -/
