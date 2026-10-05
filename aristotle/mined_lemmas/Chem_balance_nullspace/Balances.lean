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

/-- A chemical reaction with stoichiometric matrix `A` (rows indexed by chemical elements,
columns indexed by chemical species, entry `A i j` = number of atoms of element `i` in one
molecule of species `j`, counted with sign for reactants/products) *balances* if one can assign
strictly positive amounts `x j` to the species so that every element is conserved,
i.e. `A.mulVec x = 0`. -/

def Balances {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Prop :=
  ∃ x : Fin n → ℚ, (∀ j, 0 < x j) ∧ A.mulVec x = 0

/-- Any finite family of rationals admits a common positive integer denominator:
there is `d > 0` such that `d * x j` is an integer for every `j`. -/
