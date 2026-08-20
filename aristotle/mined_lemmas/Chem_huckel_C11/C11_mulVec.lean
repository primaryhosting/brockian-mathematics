import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Finset Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₁₁`, with vertices indexed by `ZMod 11`:
vertex `i` is adjacent to `i + 1` and `i - 1`. -/

lemma C11_mulVec (v : ZMod 11 → ℂ) (i : ZMod 11) :
    (C11 *ᵥ v) i = v (i + 1) + v (i - 1) := by
  have hne : ∀ i : ZMod 11, (i + 1 : ZMod 11) ≠ i - 1 := by decide
  have key : ∀ j : ZMod 11,
      C11 i j * v j = (if j = i + 1 then v j else 0) + (if j = i - 1 then v j else 0) := by
    intro j
    by_cases h1 : j = i + 1
    · simp [C11, h1, hne i]
    · by_cases h2 : j = i - 1 <;> simp [C11, h1, h2, Ne.symm (hne i)]
  rw [Matrix.mulVec, dotProduct, Finset.sum_congr rfl (fun j _ => key j),
    Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (i + 1) v,
    Finset.sum_ite_eq' Finset.univ (i - 1) v]
  simp

/-- The columns of `F` are eigenvectors of the adjacency matrix. -/
