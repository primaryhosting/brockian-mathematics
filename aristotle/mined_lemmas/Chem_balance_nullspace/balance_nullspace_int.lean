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

