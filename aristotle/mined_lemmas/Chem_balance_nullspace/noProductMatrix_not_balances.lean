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
Target: `Chem.balance_nullspace`
Provenance: Aristotle theorem prover (Harmonic)

A chemical reaction is encoded by its stoichiometric matrix `A` (rows = chemical elements,
columns = chemical species, `A i j` = signed number of atoms of element `i` in species `j`).
The reaction *balances* when the species can be given strictly positive amounts so that every
element is conserved.  A priori those amounts are arbitrary positive numbers (a chemist solving
the linear system by Gaussian elimination gets rational ones), whereas a chemical equation must
be written with positive *integer* coefficients.

`Chem.balance_nullspace` says these two notions agree: a reaction balances if and only if its
stoichiometric matrix has a strictly positive integer null vector.  The nontrivial direction
clears denominators, multiplying a positive rational solution by the product of its
denominators.
-/

namespace Chem

variable {m n : ℕ}

/-- A reaction with stoichiometric matrix `A` *balances* if strictly positive (rational)
amounts of the species can be chosen so that every element is conserved. -/

theorem noProductMatrix_not_balances : ¬ Balances noProductMatrix := by
  rintro ⟨x, hx, h⟩
  have h0 := h 0
  have hx0 := hx 0
  simp [noProductMatrix, Fin.sum_univ_succ] at h0
  simp_all

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

