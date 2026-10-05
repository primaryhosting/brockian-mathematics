/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex Matrix Polynomial

namespace Chem

/-- The adjacency matrix of the cycle graph `C₂₀`, with vertices indexed by `ZMod 20`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`.  In Hückel theory (with `α = 0`,
`β = 1`) this is the Hückel matrix of the annulene `C₂₀`. -/

lemma C20adj_mulVec (v : ZMod 20 → ℂ) (i : ZMod 20) :
    (C20adj *ᵥ v) i = v (i + 1) + v (i - 1) := by
  have hne : (i + 1) ≠ (i - 1) := by
    intro h
    have h2 : (2 : ZMod 20) = 0 := by linear_combination h
    revert h2; decide
  have key : ∀ j : ZMod 20, C20adj i j * v j
      = (if j = i + 1 then v j else 0) + (if j = i - 1 then v j else 0) := by
    intro j
    rcases eq_or_ne j (i + 1) with h1 | h1
    · subst h1; simp [C20adj, hne]
    · rcases eq_or_ne j (i - 1) with h2 | h2
      · subst h2; simp [C20adj, Ne.symm hne]
      · simp [C20adj, h1, h2]
  simp only [Matrix.mulVec, dotProduct, key, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ (i + 1) v, Finset.sum_ite_eq' Finset.univ (i - 1) v]
  simp

/-- If `a ^ 20 = 1`, then `a ^ (n % 20) = a ^ n`. -/
