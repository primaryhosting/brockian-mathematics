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

theorem balanceable_of_rat (A : Matrix (Fin m) (Fin n) ℤ)
    (q : Fin n → ℚ) (hq : ∀ j, 0 < q j) (hker : ∀ i, ∑ j, (A i j : ℚ) * q j = 0) :
    IsBalanceable A := by
  classical
  set d : ℕ := ∏ j, (q j).den with hd
  have hdpos : 0 < d := Finset.prod_pos fun j _ => (q j).pos
  set x : Fin n → ℤ := fun j => (q j).num * ((d / (q j).den : ℕ) : ℤ) with hx
  have key : ∀ j, ((x j : ℤ) : ℚ) = q j * d := by
    intro j
    have hdvd : (q j).den ∣ d := Finset.dvd_prod_of_mem (fun j => (q j).den) (mem_univ j)
    obtain ⟨c, hc⟩ := hdvd
    have hden : (d / (q j).den : ℕ) = c := by
      rw [hc, Nat.mul_div_cancel_left _ (q j).pos]
    rw [hx]
    simp only [hden]
    rw [hc]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  have hdQ : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hdpos
  refine ⟨x, fun j => ?_, fun i => ?_⟩
  · have : (0 : ℚ) < ((x j : ℤ) : ℚ) := by rw [key j]; exact mul_pos (hq j) hdQ
    exact_mod_cast this
  · have hsum : ((∑ j, A i j * x j : ℤ) : ℚ) = 0 := by
      rw [Int.cast_sum]
      calc ∑ j, ((A i j * x j : ℤ) : ℚ)
          = ∑ j, (A i j : ℚ) * (q j * d) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Int.cast_mul, key j]
        _ = (d : ℚ) * ∑ j, (A i j : ℚ) * q j := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hker i, mul_zero]
    exact_mod_cast hsum

/-- Balanceability over `ℤ` and over `ℚ` agree: a reaction admits strictly positive integer
stoichiometric coefficients iff it admits strictly positive rational ones. -/
