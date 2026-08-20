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
