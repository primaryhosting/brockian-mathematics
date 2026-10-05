import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Real Matrix Finset

/-- A primitive 18-th root of unity. -/

lemma AU : C18adj * U = U * Dg := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hne : j + 1 ≠ j - 1 := by
    intro h
    have : (2 : ZMod 18) = 0 := by linear_combination h
    exact absurd this (by decide)
  have hsplit : ∀ i : ZMod 18, C18adj j i * U i k
      = (if i = j + 1 then ee (i * k) else 0) + (if i = j - 1 then ee (i * k) else 0) := by
    intro i
    simp only [C18adj, U, Matrix.of_apply]
    by_cases h1 : i = j + 1
    · rw [if_pos h1, if_pos (Or.inl h1), if_neg (by rw [h1]; exact hne)]
      ring
    · by_cases h2 : i = j - 1
      · rw [if_neg h1, if_pos h2, if_pos (Or.inr h2)]
        ring
      · rw [if_neg h1, if_neg h2, if_neg (by tauto)]
        ring
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (j + 1) (fun i => ee (i * k)),
    Finset.sum_ite_eq' Finset.univ (j - 1) (fun i => ee (i * k))]
  simp only [Finset.mem_univ, if_true]
  rw [Dg, Matrix.diagonal_apply]
  have hsum : ∑ l : ZMod 18, U j l * (if l = k then ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) else 0)
      = U j k * ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [show (∑ l : ZMod 18, U j l * (if k = l then ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) else 0))
      = ∑ l : ZMod 18, U j l * (if l = k then ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) else 0) from
      Finset.sum_congr rfl (fun l _ => by by_cases h : l = k <;> simp [h, eq_comm]), hsum]
  simp only [U, Matrix.of_apply]
  rw [show (j + 1) * k = j * k + k by ring, show (j - 1) * k = j * k + -k by ring,
    ee_add, ee_add, ← mul_add, ee_add_neg]

/-- **Hückel theory for the cycle `C₁₈`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₈` if and only if `μ = 2 cos (2πk/18)` for some
`k ∈ {0, …, 17}`. -/
