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

