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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

/-- A *stoichiometric matrix* `A : Matrix (Fin m) (Fin n) ℤ` records, for each of the `m`
chemical elements (rows) and each of the `n` species (columns), the signed number of atoms
of that element contributed by one unit of that species (reactants counted positively,
products negatively, say).

A vector of coefficients `x` *balances* the reaction if all coefficients are strictly
positive and every element's atom count cancels, i.e. `A.mulVec x = 0`. -/
def BalancedInt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (x : Fin n → ℤ) : Prop :=
  (∀ j, 0 < x j) ∧ A.mulVec x = 0

/-- The same balance condition, but allowing rational (fractional) coefficients. -/
def BalancedRat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (y : Fin n → ℚ) : Prop :=
  (∀ j, 0 < y j) ∧ (A.map (fun a : ℤ => (a : ℚ))).mulVec y = 0

/-- A reaction *balances* if it admits a strictly positive rational solution of the
stoichiometric equations. -/
def Balances {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∃ y : Fin n → ℚ, BalancedRat A y

/-- Any finite family of rationals admits a common positive denominator. -/
theorem exists_common_denom {n : ℕ} (y : Fin n → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∀ j, ∃ k : ℤ, (d : ℚ) * y j = (k : ℚ) := by
  refine ⟨∏ j : Fin n, (y j).den, ?_, ?_⟩
  · exact Finset.prod_pos fun j _ => (y j).pos
  · intro j
    obtain ⟨c, hc⟩ : ((y j).den : ℤ) ∣ (∏ j : Fin n, (y j).den : ℕ) := by
      exact_mod_cast Int.natCast_dvd_natCast.mpr
        (Finset.dvd_prod_of_mem (fun j : Fin n => (y j).den) (Finset.mem_univ j))
    refine ⟨c * (y j).num, ?_⟩
    have hden : ((y j).den : ℚ) ≠ 0 := by
      exact_mod_cast (y j).den_nz
    have hy : ((y j).num : ℚ) = (y j) * ((y j).den : ℚ) :=
      (div_eq_iff hden).mp (Rat.num_div_den (y j))
    have hcast : ((∏ j : Fin n, (y j).den : ℕ) : ℚ) = ((y j).den : ℚ) * (c : ℚ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hc
    rw [hcast]
    push_cast [hy]
    ring

/-- **Balance nullspace theorem.**  A chemical reaction balances (i.e. has a strictly positive
rational solution of its stoichiometric equations) if and only if its stoichiometric matrix has
a strictly positive *integer* null vector. -/
theorem balance_nullspace {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Balances A ↔ ∃ x : Fin n → ℤ, BalancedInt A x := by
  constructor
  · rintro ⟨y, hpos, hnull⟩
    obtain ⟨d, hd, hdy⟩ := exists_common_denom y
    choose k hk using hdy
    have hkq : ∀ j, (k j : ℚ) = (d : ℚ) * y j := fun j => (hk j).symm
    have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
    refine ⟨k, ?_, ?_⟩
    · intro j
      have : (0 : ℚ) < (k j : ℚ) := by
        rw [hkq j]; exact mul_pos hdq (hpos j)
      exact_mod_cast this
    · funext i
      have hi : ∑ j : Fin n, (A i j : ℚ) * y j = 0 := by
        have := congrFun hnull i
        simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using this
      have : ((A.mulVec k i : ℤ) : ℚ) = 0 := by
        have : ((A.mulVec k i : ℤ) : ℚ) = (d : ℚ) * ∑ j : Fin n, (A i j : ℚ) * y j := by
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          push_cast
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hkq j]; ring
        rw [this, hi, mul_zero]
      have h0 : A.mulVec k i = 0 := by exact_mod_cast this
      simpa using h0
  · rintro ⟨x, hpos, hnull⟩
    refine ⟨fun j => ((x j : ℤ) : ℚ), ?_, ?_⟩
    · intro j
      show (0 : ℚ) < ((x j : ℤ) : ℚ)
      exact_mod_cast hpos j
    · funext i
      have := congrFun hnull i
      have h : ((A.mulVec x i : ℤ) : ℚ) = 0 := by
        simpa using congrArg (fun z : ℤ => (z : ℚ)) this
      simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using h

/-- Sanity check that the definitions are satisfiable: the reaction
`2 H₂ + O₂ → 2 H₂O` balances, with stoichiometric matrix rows indexed by the
elements `H, O` and columns by the species `H₂, O₂, H₂O` (products carry a minus sign). -/
theorem water_balances :
    Balances (Matrix.of ![![2, 0, -2], ![0, 2, -1]] : Matrix (Fin 2) (Fin 3) ℤ) := by
  refine ⟨![2, 1, 2], ?_, ?_⟩
  · intro j
    fin_cases j <;> norm_num
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.map_apply]

end Chem

