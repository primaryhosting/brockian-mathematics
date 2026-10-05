/-
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` commands to precede any module docstring, so the header above is a
-- plain block comment; the same text is repeated as the module docstring below.)

import Mathlib

/-!
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix

/-- A chemical reaction is described by its *stoichiometric matrix* `S`: the entry `S i j`
records how many atoms of element `i` occur in one unit of species `j`
(signed: negative for reactants, positive for products, say).

The reaction *balances* if one can choose strictly positive amounts `x j` of each species so
that every element is conserved, i.e. `S.mulVec x = 0`. -/
def Balances {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℚ) : Prop :=
  ∃ x : Fin n → ℚ, (∀ j, 0 < x j) ∧ S.mulVec x = 0

/-- Any finite family of rationals admits a positive common denominator. -/
theorem exists_common_denom {n : ℕ} (y : Fin n → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ j, ∃ z : ℤ, (N : ℚ) * y j = (z : ℚ) := by
  refine ⟨∏ j, (y j).den, Finset.prod_pos fun j _ => (y j).pos, fun j => ?_⟩
  refine ⟨(∏ i ∈ Finset.univ.erase j, (y i).den) * (y j).num, ?_⟩
  have hprod : ∏ i, (y i).den = (y j).den * ∏ i ∈ Finset.univ.erase j, (y i).den :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
  rw [hprod]
  push_cast
  rw [mul_comm ((y j).den : ℚ), mul_assoc, Rat.den_mul_eq_num]

/-- **Balance nullspace.**  A chemical reaction balances (i.e. its stoichiometric matrix admits a
strictly positive rational vector of amounts in its kernel) if and only if the stoichiometric
matrix has a strictly positive *integer* null vector. -/
theorem balance_nullspace {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℚ) :
    Balances S ↔ ∃ x : Fin n → ℤ, (∀ j, 0 < x j) ∧ S.mulVec (fun j => (x j : ℚ)) = 0 := by
  constructor
  · rintro ⟨y, hy, hSy⟩
    obtain ⟨N, hN, hz⟩ := exists_common_denom y
    choose z hzy using hz
    refine ⟨z, fun j => ?_, ?_⟩
    · have h1 : (0 : ℚ) < (z j : ℚ) := by
        rw [← hzy j]
        exact mul_pos (by exact_mod_cast hN) (hy j)
      exact_mod_cast h1
    · have : (fun j => ((z j : ℚ))) = (N : ℚ) • y := by
        funext j; rw [Pi.smul_apply, smul_eq_mul, hzy j]
      rw [this, Matrix.mulVec_smul, hSy, smul_zero]
  · rintro ⟨x, hx, hSx⟩
    exact ⟨fun j => (x j : ℚ), fun j => by simpa using (Int.cast_lt (R := ℚ)).2 (hx j), hSx⟩

/-- Integer form of the previous theorem: for a stoichiometric matrix with integer entries
(the usual situation, the entries being atom counts), the reaction balances if and only if the
integer matrix `S` has a strictly positive integer null vector. -/
theorem balance_nullspace_int {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℤ) :
    Balances (S.map (fun a => (a : ℚ))) ↔ ∃ x : Fin n → ℤ, (∀ j, 0 < x j) ∧ S.mulVec x = 0 := by
  have key : ∀ x : Fin n → ℤ, ∀ i,
      (S.map (fun a => (a : ℚ))).mulVec (fun j => (x j : ℚ)) i = ((S.mulVec x i : ℤ) : ℚ) := by
    intro x i
    simp [Matrix.mulVec, dotProduct]
  rw [balance_nullspace]
  constructor
  · rintro ⟨x, hx, hSx⟩
    refine ⟨x, hx, funext fun i => ?_⟩
    have := congrFun hSx i
    rw [key x i] at this
    have h0 : ((S.mulVec x i : ℤ) : ℚ) = 0 := by simpa using this
    simpa using (by exact_mod_cast h0 : S.mulVec x i = 0)
  · rintro ⟨x, hx, hSx⟩
    refine ⟨x, hx, funext fun i => ?_⟩
    rw [key x i, congrFun hSx i]
    simp

/-- Sanity check: the reaction `2 H₂ + O₂ → 2 H₂O` balances.
Rows are the elements `H`, `O`; columns are the species `H₂`, `O₂`, `H₂O`
(reactants counted positively, products negatively). -/
example : Balances (Matrix.of ![![2, 0, -2], ![0, 2, -1]] : Matrix (Fin 2) (Fin 3) ℚ) := by
  refine ⟨![2, 1, 2], ?_, ?_⟩
  · intro j; fin_cases j <;> norm_num
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end Chem

import Mathlib

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

