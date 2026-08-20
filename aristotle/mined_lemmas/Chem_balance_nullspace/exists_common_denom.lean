import Mathlib

/-!
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

variable {m n : ℕ}

/-- `A` is the *stoichiometric matrix* of a reaction: rows are elements, columns are chemical
species, and `A i j` is the (signed) number of atoms of element `i` in species `j`.  A vector
`x` of stoichiometric coefficients *conserves* every element when each row of `A` is orthogonal
to `x`. -/

theorem exists_common_denom (x : Fin n → ℚ) (hx : ∀ j, 0 < x j) :
    ∃ (k : ℤ) (z : Fin n → ℤ), 0 < k ∧ (∀ j, 0 < z j) ∧ ∀ j, (z j : ℚ) = (k : ℚ) * x j := by
  classical
  set K : ℕ := ∏ j, (x j).den with hK
  have hKpos : 0 < K := Finset.prod_pos fun j _ => (x j).pos
  -- for each `j`, choose the cofactor `c j` with `K = (x j).den * c j`
  have hdvd : ∀ j : Fin n, (x j).den ∣ K := fun j =>
    Finset.dvd_prod_of_mem (fun j => (x j).den) (Finset.mem_univ j)
  choose c hc using hdvd
  have hcpos : ∀ j, 0 < c j := by
    intro j
    rcases Nat.eq_zero_or_pos (c j) with h | h
    · exact absurd (hc j) (by simp [h, hKpos.ne'])
    · exact h
  refine ⟨(K : ℤ), fun j => (c j : ℤ) * (x j).num, by exact_mod_cast hKpos, ?_, ?_⟩
  · intro j
    exact mul_pos (by exact_mod_cast hcpos j) (Rat.num_pos.mpr (hx j))
  · intro j
    have h1 : ((K : ℚ)) = ((x j).den : ℚ) * (c j : ℚ) := by
      exact_mod_cast congrArg (fun t : ℕ => (t : ℚ)) (hc j)
    have h2 : x j * ((x j).den : ℚ) = ((x j).num : ℚ) := Rat.mul_den_eq_num (x j)
    push_cast
    rw [h1]
    calc (c j : ℚ) * ((x j).num : ℚ)
        = (c j : ℚ) * (x j * ((x j).den : ℚ)) := by rw [h2]
      _ = ((x j).den : ℚ) * (c j : ℚ) * x j := by ring

/-- **A chemical reaction balances iff its stoichiometric matrix has a positive integer null
vector.**  Here `Balances A` says that some strictly positive *rational* coefficient vector
conserves every element; the right-hand side produces strictly positive *integer*
stoichiometric coefficients lying in the null space (kernel) of the stoichiometric matrix. -/
