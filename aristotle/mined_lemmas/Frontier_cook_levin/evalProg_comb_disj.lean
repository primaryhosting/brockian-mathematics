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

theorem evalProg_comb_disj (p q : List Gate) (x : ℕ → Bool) (hp : p ≠ []) (hq : q ≠ []) :
    evalProg (comb Gate.disj p q) x = (evalProg p x || evalProg q x) := by
  have hp' : 0 < p.length := List.length_pos_iff.2 hp
  have hq' : 0 < q.length := List.length_pos_iff.2 hq
  rw [evalProg_comb]
  have e1 : (vals p x ++ vals q x).getD (p.length - 1) false = evalProg p x := by
    rw [List.getD_append _ _ _ _ (by rw [vals_length]; omega)]
    rfl
  have e2 : (vals p x ++ vals q x).getD (p.length + q.length - 1) false = evalProg q x := by
    have : p.length + q.length - 1 = (vals p x).length + (q.length - 1) := by
      rw [vals_length]; omega
    rw [this, getD_append_add]
    rfl
  simp only [gateVal, e1, e2]

