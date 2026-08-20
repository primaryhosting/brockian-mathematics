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

theorem evalProg_comb (op : ℕ → ℕ → Gate) (p q : List Gate) (x : ℕ → Bool) :
    evalProg (comb op p q) x =
      gateVal x (vals p x ++ vals q x) (op (p.length - 1) (p.length + q.length - 1)) := by
  have hlen : (vals p x ++ vals q x).length = p.length + q.length := by
    simp [vals_length]
  rw [evalProg, vals_comb, comb_length]
  have : p.length + q.length + 1 - 1 = (vals p x ++ vals q x).length + 0 := by
    simp [hlen]
  rw [this, getD_append_add]
  simp

