/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset

/-- A primitive 15-th root of unity. -/

lemma C15adj_mulVec (v : ZMod 15 → ℂ) (i : ZMod 15) :
    (C15adj *ᵥ v) i = v (i + 1) + v (i - 1) := by
  have hsplit : ∀ j : ZMod 15,
      C15adj i j * v j = (if j = i + 1 then v j else 0) + (if j = i - 1 then v j else 0) := by
    intro j
    by_cases h1 : j = i + 1 <;> by_cases h2 : j = i - 1 <;>
      simp [C15adj, h1, h2]
    · exfalso
      have : (i : ZMod 15) + 1 = i - 1 := by rw [← h1, h2]
      have h3 : (2 : ZMod 15) = 0 := by linear_combination this
      exact absurd h3 (by decide)
  rw [Matrix.mulVec, Matrix.dotProduct]
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (i + 1) v, Finset.sum_ite_eq' Finset.univ (i - 1) v]
  simp

/-- **Hückel theory for the cycle `C₁₅`**: a complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph on 15 vertices if and only if it is of the form
`2 cos (2 π k / 15)` for some `k ∈ {0, …, 14}`. -/
