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

set_option grind.warning false

namespace Chem

/-- A chemical reaction over `m` chemical elements and `n` chemical species.

`comp i e` is the number of atoms of element `e` in one formula unit of species `i`,
and `isProduct i` says whether species `i` sits on the product side of the reaction
(otherwise it is a reactant). -/
structure Reaction (m n : ℕ) where
  /-- `comp i e` = number of atoms of element `e` in one unit of species `i`. -/
  comp : Fin n → Fin m → ℕ
  /-- whether species `i` is on the product side. -/
  isProduct : Fin n → Bool

variable {m n : ℕ}

/-- The stoichiometric matrix of a reaction: rows are elements, columns are species,
the entry being the atom count of the element in the species, signed `+` for products
and `-` for reactants. -/

def water : Reaction 2 3 where
  comp := ![![2, 0], ![0, 2], ![2, 1]]
  isProduct := ![false, false, true]

example : water.Balances := by
  refine ⟨![2, 1, 2], ?_, ?_⟩
  · decide
  · decide

/-- `H₂ → O₂` cannot be balanced. -/
