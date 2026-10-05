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
