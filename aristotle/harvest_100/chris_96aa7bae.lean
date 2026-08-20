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
def Balances (A : Matrix (Fin m) (Fin n) ℤ) (x : Fin n → ℤ) : Prop :=
  ∀ i, ∑ j, A i j * x j = 0

/-- A reaction is *balanceable* if some vector of strictly positive integer coefficients
balances it. -/
def IsBalanceable (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∃ x : Fin n → ℤ, (∀ j, 0 < x j) ∧ Balances A x

/-- **Balance nullspace.** A chemical reaction balances (with strictly positive integer
coefficients) if and only if its stoichiometric matrix has a strictly positive integer vector
in its kernel (null space). -/
theorem balance_nullspace (A : Matrix (Fin m) (Fin n) ℤ) :
    IsBalanceable A ↔ ∃ x : Fin n → ℤ, (∀ j, 0 < x j) ∧ x ∈ LinearMap.ker A.mulVecLin := by
  simp only [IsBalanceable, Balances, LinearMap.mem_ker, Matrix.mulVecLin_apply,
    Matrix.mulVec, dotProduct, funext_iff, Pi.zero_apply]

/-- A strictly positive rational null vector can be scaled to a strictly positive integer null
vector (clearing denominators). -/
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
theorem water_isBalanceable :
    IsBalanceable (Matrix.of ![![2, 0, -2], ![0, 2, -1]] : Matrix (Fin 2) (Fin 3) ℤ) :=
  ⟨![2, 1, 2], by decide, fun i => by fin_cases i <;> decide⟩

/-- A concrete unbalanceable "reaction": `H₂ → O₂` (hydrogen on both sides is impossible to
cancel because the H row is nonnegative and nonzero). -/
theorem not_isBalanceable_example :
    ¬ IsBalanceable (Matrix.of ![![2, 0], ![0, 2]] : Matrix (Fin 2) (Fin 2) ℤ) :=
  not_isBalanceable_of_row_nonneg _ 0 (fun j => by fin_cases j <;> decide) 0 (by decide)

end Chem

import Mathlib
import RequestProject.BalanceNullspace

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

-- The target theorem, proved in `RequestProject/BalanceNullspace.lean`.
#check @Chem.balance_nullspace
#print axioms Chem.balance_nullspace

