/-
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
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

set_option grind.warning false

namespace Frontier

/-! ## CNF formulas -/

/-- A literal: a variable index together with a sign (`true` = positive). -/
abbrev Lit : Type := ℕ × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause : Type := List Lit

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF : Type := List Clause

/-- Value of a literal under an assignment. -/

theorem vals_getD_step (p : List Gate) (x : ℕ → Bool) {j : ℕ} (hj : j < p.length) :
    (vals p x).getD j false =
      gateVal x (vals (p.take j) x) (p.getD j (.cst false)) := by
  have hlen : (vals (p.take j) x).length = j := by
    rw [vals_length, List.length_take]; omega
  have hd : p.drop j = p.getD j (.cst false) :: p.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hj, List.getD_eq_getElem p (.cst false) hj]
  have hsplit : vals p x =
      evalAux x (p.drop (j + 1))
        (vals (p.take j) x ++ [gateVal x (vals (p.take j) x) (p.getD j (.cst false))]) := by
    have h : p = p.take j ++ p.drop j := (List.take_append_drop j p).symm
    simp only [vals]
    conv_lhs => rw [h]
    rw [evalAux_append, hd]
    simp only [evalAux]
  have hpref := evalAux_prefix x (p.drop (j + 1))
      (vals (p.take j) x ++ [gateVal x (vals (p.take j) x) (p.getD j (.cst false))])
  rw [← hsplit] at hpref
  rw [getD_of_prefix hpref (k := j) (by simp [hlen])]
  exact getD_append_singleton _ _ _ hlen

