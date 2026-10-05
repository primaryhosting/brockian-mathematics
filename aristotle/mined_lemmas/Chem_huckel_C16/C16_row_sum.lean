/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Polynomial SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of a
16-membered annulene, with `α = 0`, `β = 1`). -/

lemma C16_row_sum (f : Fin 16 → ℂ) (j : Fin 16) :
    ∑ l, C16 j l * f l = f (j - 1) + f (j + 1) := by
  have hfilter : ∀ j : Fin 16,
      Finset.univ.filter (fun l : Fin 16 => l = j - 1 ∨ l = j + 1) = {j - 1, j + 1} := by decide
  have hne : ∀ j : Fin 16, j - 1 ≠ j + 1 := by decide
  have : ∑ l, C16 j l * f l = ∑ l ∈ Finset.univ.filter
      (fun l : Fin 16 => l = j - 1 ∨ l = j + 1), f l := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [C16_apply]
    split <;> simp
  rw [this, hfilter j, Finset.sum_pair (hne j)]

/-- The key diagonalization identity `A · U = U · D`. -/
