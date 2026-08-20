import Mathlib

/-!
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset

variable {m n : ℕ}

/-- `Balances A x` says that the (signed) stoichiometric coefficient vector `x` balances the
reaction whose stoichiometric matrix is `A`: for every element `i` (row of `A`), the total
number of atoms of that element created minus destroyed is zero. -/

theorem not_isBalanceable_of_row_nonneg (A : Matrix (Fin m) (Fin n) ℤ) (i : Fin m)
    (hnonneg : ∀ j, 0 ≤ A i j) (j₀ : Fin n) (hpos : 0 < A i j₀) :
    ¬ IsBalanceable A := by
  rintro ⟨x, hx, hbal⟩
  have hsum : 0 < ∑ j, A i j * x j :=
    Finset.sum_pos' (fun j _ => mul_nonneg (hnonneg j) (hx j).le)
      ⟨j₀, Finset.mem_univ _, mul_pos hpos (hx j₀)⟩
  rw [hbal i] at hsum
  exact lt_irrefl 0 hsum

/-- The reaction `2 H₂ + O₂ → 2 H₂O` balances.  Columns are the species `H₂, O₂, H₂O`
(products carry negative signs), rows are the elements `H, O`. -/
