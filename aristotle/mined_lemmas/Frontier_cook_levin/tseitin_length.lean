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

theorem tseitin_length (p : List Gate) : (tseitin p).length ≤ 3 * p.length + 3 := by
  have hsum : ((List.range p.length).flatMap
      (fun j => gateClauses j (p.getD j (.cst false)))).length ≤ 3 * p.length := by
    rw [List.length_flatMap]
    have h1 := sum_le_of_forall_le
      ((List.range p.length).map
        (fun j => (gateClauses j (p.getD j (.cst false))).length)) 3 (by
          intro y hy
          simp only [List.mem_map] at hy
          obtain ⟨j, _, rfl⟩ := hy
          exact gateClauses_card _ _)
    have h2 : ((List.range p.length).map
        (fun j => (gateClauses j (p.getD j (.cst false))).length)).length = p.length := by
      simp
    rw [h2] at h1
    omega
  have hif : (if p.isEmpty then [([] : Clause)] else []).length ≤ 1 := by
    split <;> simp
  simp only [tseitin, List.length_cons, List.length_append]
  omega

