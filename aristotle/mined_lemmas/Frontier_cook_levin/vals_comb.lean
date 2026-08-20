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

theorem vals_comb (op : ℕ → ℕ → Gate) (p q : List Gate) (x : ℕ → Bool) :
    vals (comb op p q) x =
      (vals p x ++ vals q x) ++
        [gateVal x (vals p x ++ vals q x) (op (p.length - 1) (p.length + q.length - 1))] := by
  have h1 : vals (p ++ q.map (shiftGate p.length)) x = vals p x ++ vals q x := by
    have := evalAux_map_shift x q (vals p x) []
    simp only [vals] at *
    rw [evalAux_append]
    rw [show (evalAux x p [] : List Bool) = evalAux x p [] ++ [] by simp] at *
    simpa [vals_length, evalAux_length] using this
  simp only [comb, vals] at *
  rw [evalAux_append, h1]
  simp [evalAux]

/-! ## Tseitin transformation -/

/-- CNF variable holding the value of program input `i`. -/
