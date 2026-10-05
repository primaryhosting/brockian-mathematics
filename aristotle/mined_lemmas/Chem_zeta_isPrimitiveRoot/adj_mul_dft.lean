import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The adjacency matrix of the cycle graph `C₁₃`, with vertices indexed by `ZMod 13`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`. -/

lemma adj_mul_dft : adjC13 * dft = dft * Matrix.diagonal mu := by
  ext i k
  have hne : (i + 1 : ZMod 13) ≠ i - 1 := by
    intro h
    have h2 : (2 : ZMod 13) = 0 := by linear_combination h
    exact absurd h2 (by decide)
  have hterm : ∀ j : ZMod 13, adjC13 i j * dft j k =
      (if j = i + 1 then dft j k else 0) + (if j = i - 1 then dft j k else 0) := by
    intro j
    by_cases h1 : j = i + 1
    · subst h1
      simp [adjC13, hne]
    · by_cases h2 : j = i - 1
      · subst h2
        simp [adjC13, Ne.symm hne]
      · simp [adjC13, h1, h2]
  rw [Matrix.mul_apply]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (i + 1) (fun j => dft j k),
    Finset.sum_ite_eq' Finset.univ (i - 1) (fun j => dft j k)]
  simp only [Finset.mem_univ, if_true, Matrix.mul_diagonal]
  show ee ((i + 1) * k) + ee ((i - 1) * k) = ee (i * k) * mu k
  have e1 : (i + 1) * k = i * k + k := by ring
  have e2 : (i - 1) * k = i * k + (-k) := by ring
  rw [e1, e2, ee_add, ee_add, mu, mul_add]

