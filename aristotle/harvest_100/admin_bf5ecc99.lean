/-
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

/-- A stoichiometric matrix `A : Matrix (Fin m) (Fin n) ℤ` records, in entry `A i j`, the number
of atoms of element `i` occurring in one unit of species `j` (signed: reactants positive,
products negative, say).  The reaction *balances* if some assignment of strictly positive
rational stoichiometric coefficients to the species conserves every element, i.e. lies in the
null space of `A`. -/
def Balances {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∃ x : Fin n → ℚ, (∀ j, 0 < x j) ∧ (A.map (fun a : ℤ => (a : ℚ))).mulVec x = 0

/-- **Balance nullspace theorem.**  A chemical reaction balances (has strictly positive
rational stoichiometric coefficients conserving every element) if and only if its
stoichiometric matrix has a strictly positive *integer* null vector. -/
theorem balance_nullspace {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Balances A ↔ ∃ z : Fin n → ℤ, (∀ j, 0 < z j) ∧ A.mulVec z = 0 := by
  constructor
  · rintro ⟨x, hxpos, hx⟩
    -- Clear denominators with the common denominator `d = ∏ j, (x j).den`.
    set d : ℤ := ∏ j, ((x j).den : ℤ) with hd
    have hdpos : 0 < d := Finset.prod_pos (by intro j _; exact_mod_cast (x j).pos)
    have key : ∀ j, ∃ z : ℤ, (d : ℚ) * x j = z := by
      intro j
      have hdvd : ((x j).den : ℤ) ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨c * (x j).num, ?_⟩
      rw [hc]
      push_cast
      rw [mul_comm ((x j).den : ℚ) (c : ℚ), mul_assoc]
      congr 1
      rw [mul_comm]
      exact_mod_cast Rat.mul_den_eq_num (x j)
    choose z hz using key
    refine ⟨z, ?_, ?_⟩
    · intro j
      have : (0 : ℚ) < (z j : ℚ) := by
        rw [← hz j]
        exact mul_pos (by exact_mod_cast hdpos) (hxpos j)
      exact_mod_cast this
    · funext i
      have hxi : ∑ j, (A i j : ℚ) * x j = 0 := by
        have := congrFun hx i
        simpa [Matrix.mulVec, dotProduct, Matrix.map] using this
      have hcast : ((A.mulVec z i : ℤ) : ℚ) = 0 := by
        simp only [Matrix.mulVec, dotProduct]
        push_cast
        calc ∑ j, (A i j : ℚ) * (z j : ℚ)
            = ∑ j, (A i j : ℚ) * ((d : ℚ) * x j) :=
              Finset.sum_congr rfl fun j _ => by rw [hz j]
          _ = (d : ℚ) * ∑ j, (A i j : ℚ) * x j := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by ring
          _ = 0 := by rw [hxi, mul_zero]
      simpa using hcast
  · rintro ⟨z, hzpos, hz⟩
    refine ⟨fun j => (z j : ℚ), fun j => by
      simpa using (Int.cast_pos (R := ℚ)).mpr (hzpos j), ?_⟩
    funext i
    have h1 : ∑ j, A i j * z j = 0 := by
      simpa [Matrix.mulVec, dotProduct] using congrFun hz i
    have h2 : ((∑ j, A i j * z j : ℤ) : ℚ) = 0 := by rw [h1]; simp
    push_cast at h2
    simpa [Matrix.mulVec, dotProduct, Matrix.map] using h2

end Chem

