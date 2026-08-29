/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring; the header above is
-- repeated below as the module docstring.)
import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Finset

namespace Chem

/-- The standard additive character of `ZMod 11`, `x ↦ exp (2πI x / 11)`. -/
local notation "χ" => (ZMod.stdAddChar : AddChar (ZMod 11) ℂ)

/-- The Hückel eigenvalues of the cycle `C₁₁`. -/

lemma Adj11_mul_Fmat : Adj11 * Fmat = Fmat * Matrix.diagonal lam := by
  ext i k
  have hne : (i + 1 : ZMod 11) ≠ i - 1 := by decide +kernel
  have hsplit : ∀ j : ZMod 11, Adj11 i j * Fmat j k
      = (if j = i + 1 then χ (j * k) else 0) + (if j = i - 1 then χ (j * k) else 0) := by
    intro j
    simp only [Adj11, Fmat, Matrix.of_apply]
    by_cases h1 : j = i + 1 <;> by_cases h2 : j = i - 1 <;>
      simp_all
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (i + 1),
    Finset.sum_ite_eq' Finset.univ (i - 1), Finset.mem_univ, if_true]
  have hd : ∀ j : ZMod 11, Fmat i j * Matrix.diagonal lam j k
      = if j = k then χ (i * k) * lam k else 0 := by
    intro j
    by_cases h : j = k
    · subst h; simp [Fmat, Matrix.diagonal]
    · simp [Matrix.diagonal, h]
  rw [Finset.sum_congr rfl (fun j _ => hd j)]
  rw [Finset.sum_ite_eq' Finset.univ k, if_pos (Finset.mem_univ k)]
  have e1 : ((i + 1 : ZMod 11) * k) = i * k + k := by ring
  have e2 : ((i - 1 : ZMod 11) * k) = i * k + (-k) := by ring
  rw [e1, e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ← mul_add, char_add_char_neg]

/-- Eigenvalue characterisation for the `ZMod 11` version of the adjacency matrix. -/
