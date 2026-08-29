/-
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

open Finset

/-- A chemical reaction with `n` species over `m` elements, described by its stoichiometric
matrix `A` (row `k` records how many atoms of element `k` each species contributes), *balances*
if there is a choice of strictly positive (rational) amounts of every species that conserves
every element. -/
def Balances {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∃ x : Fin n → ℚ, (∀ i, 0 < x i) ∧ ∀ k, ∑ i, (A k i : ℚ) * x i = 0

/-- The stoichiometric matrix `A` has a *positive integer null vector* if some vector of
strictly positive integers lies in its kernel. -/
def HasPosIntNullVector {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∃ z : Fin n → ℤ, (∀ i, 0 < z i) ∧ ∀ k, ∑ i, A k i * z i = 0

/-- Any finite family of rationals can be scaled by a single positive integer so that all
entries become integers. -/
lemma exists_int_scaling {n : ℕ} (x : Fin n → ℚ) :
    ∃ (N : ℤ) (z : Fin n → ℤ), 0 < N ∧ ∀ i, (z i : ℚ) = (N : ℚ) * x i := by
  refine ⟨∏ j, ((x j).den : ℤ),
    fun i => (∏ j ∈ univ.erase i, ((x j).den : ℤ)) * (x i).num, ?_, ?_⟩
  · exact Finset.prod_pos (fun j _ => by exact_mod_cast (x j).pos)
  · intro i
    have h : ∏ j, ((x j).den : ℚ) = (∏ j ∈ univ.erase i, ((x j).den : ℚ)) * ((x i).den : ℚ) :=
      (Finset.prod_erase_mul _ _ (mem_univ i)).symm
    push_cast
    rw [h, mul_assoc, mul_comm ((x i).den : ℚ) (x i), Rat.mul_den_eq_num]

/-- **Balance nullspace theorem.** A chemical reaction balances (i.e. admits strictly positive
rational stoichiometric amounts conserving every element) if and only if its stoichiometric
matrix has a strictly positive *integer* null vector. -/
theorem balance_nullspace {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Balances A ↔ HasPosIntNullVector A := by
  constructor
  · rintro ⟨x, hxpos, hx⟩
    obtain ⟨N, z, hN, hz⟩ := exists_int_scaling x
    refine ⟨z, ?_, ?_⟩
    · intro i
      have : (0 : ℚ) < (z i : ℚ) := by
        rw [hz i]
        exact mul_pos (by exact_mod_cast hN) (hxpos i)
      exact_mod_cast this
    · intro k
      have : ∑ i, ((A k i : ℚ)) * (z i : ℚ) = 0 := by
        have : ∑ i, ((A k i : ℚ)) * (z i : ℚ) = (N : ℚ) * ∑ i, (A k i : ℚ) * x i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [hz i]; ring
        rw [this, hx k, mul_zero]
      exact_mod_cast this
  · rintro ⟨z, hzpos, hz⟩
    refine ⟨fun i => (z i : ℚ), fun i => ?_, fun k => ?_⟩
    · show (0 : ℚ) < (z i : ℚ)
      exact_mod_cast hzpos i
    · show ∑ i, ((A k i : ℚ)) * (z i : ℚ) = 0
      exact_mod_cast hz k

end Chem

