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

theorem balanceable_iff_rat (A : Matrix (Fin m) (Fin n) ℤ) :
    IsBalanceable A ↔
      ∃ q : Fin n → ℚ, (∀ j, 0 < q j) ∧ ∀ i, ∑ j, (A i j : ℚ) * q j = 0 := by
  constructor
  · rintro ⟨x, hx, hbal⟩
    refine ⟨fun j => (x j : ℚ), fun j => by simpa using (Int.cast_pos (R := ℚ)).mpr (hx j),
      fun i => ?_⟩
    have h : ((∑ j, A i j * x j : ℤ) : ℚ) = 0 := by rw [hbal i]; simp
    push_cast at h
    exact h
  · rintro ⟨q, hq, hker⟩
    exact balanceable_of_rat A q hq hker

/-- An obstruction to balancing: if some element occurs with the same sign in every species in
which it occurs at all (i.e. the corresponding row of the stoichiometric matrix is nonnegative
and not identically zero), then the reaction cannot be balanced with positive coefficients. -/
