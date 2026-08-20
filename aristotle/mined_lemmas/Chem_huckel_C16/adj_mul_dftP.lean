import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header block is placed immediately after `import Mathlib`, since Lean 4 requires
-- `import` commands to come first in a file.)

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Finset

/-- A primitive 16-th root of unity. -/

lemma adj_mul_dftP : adjC16 * dftP = dftP * Matrix.diagonal evC16 := by
  have hne : ∀ i : ZMod 16, i + 1 ≠ i - 1 := by decide
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hterm : ∀ j : ZMod 16, adjC16 i j * dftP j k =
      (if j = i + 1 then ee (j * k) else 0) + (if j = i - 1 then ee (j * k) else 0) := by
    intro j
    simp only [adjC16, dftP, Matrix.of_apply]
    rcases eq_or_ne j (i + 1) with h1 | h1
    · subst h1
      rw [if_pos (Or.inl rfl), if_pos rfl, if_neg (hne i), add_zero, one_mul]
    · rcases eq_or_ne j (i - 1) with h2 | h2
      · subst h2
        rw [if_pos (Or.inr rfl), if_neg h1, if_pos rfl, zero_add, one_mul]
      · rw [if_neg (not_or.2 ⟨h1, h2⟩), if_neg h1, if_neg h2, zero_mul, add_zero]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_true]
  have e1 : (i + 1) * k = i * k + k := by ring
  have e2 : (i - 1) * k = i * k + (-k) := by ring
  simp only [dftP, Matrix.of_apply]
  rw [e1, e2, ee_add, ee_add, ← mul_add, ee_add_ee_neg]

/-- **Hückel theory for the C₁₆ annulene ring.**
A complex number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₁₆`
if and only if `μ = 2 cos (2πk/16)` for some `k ∈ {0, …, 15}`. -/
