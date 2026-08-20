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

theorem gateClauses_true_iff (a : ℕ → Bool) (j : ℕ) (g : Gate) (X R : ℕ → Bool)
    (hX : ∀ i, a (xvar i) = X i)
    (hrefT : ∀ k, litEval a (refLit j k true) = R k)
    (hrefF : ∀ k, litEval a (refLit j k false) = !(R k)) :
    (∀ c ∈ gateClauses j g, clauseEval a c = true) ↔ a (gvar j) = gateValR X R g := by
  have hgT : litEval a ((gvar j, true) : Lit) = a (gvar j) := by simp [litEval]
  have hgF : litEval a ((gvar j, false) : Lit) = !(a (gvar j)) := by simp [litEval]
  have hXT : ∀ i, litEval a ((xvar i, true) : Lit) = X i := by
    intro i; simp [litEval, hX]
  have hXF : ∀ i, litEval a ((xvar i, false) : Lit) = !(X i) := by
    intro i; simp [litEval, hX]
  cases g with
  | inp i =>
      simp only [gateClauses, gateValR, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, clauseEval, List.any_cons, List.any_nil, hXT, hXF, hgT, hgF,
        Bool.or_false]
      cases h1 : a (gvar j) <;> cases h2 : X i <;> simp_all
  | cst b =>
      cases b <;>
        (simp only [gateClauses, gateValR, if_true, List.mem_cons, List.not_mem_nil,
          or_false, forall_eq, clauseEval, List.any_cons, List.any_nil, hgT,
          Bool.or_false]
         try simp_all)
  | neg k =>
      simp only [gateClauses, gateValR, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, clauseEval, List.any_cons, List.any_nil, hrefT, hrefF,
        hgT, hgF, Bool.or_false]
      cases h1 : a (gvar j) <;> cases h2 : R k <;> simp_all
  | conj k l =>
      simp only [gateClauses, gateValR, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, clauseEval, List.any_cons, List.any_nil, hrefT, hrefF,
        hgT, hgF, Bool.or_false]
      cases h1 : a (gvar j) <;> cases h2 : R k <;> cases h3 : R l <;> simp_all
  | disj k l =>
      simp only [gateClauses, gateValR, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, clauseEval, List.any_cons, List.any_nil, hrefT, hrefF,
        hgT, hgF, Bool.or_false]
      cases h1 : a (gvar j) <;> cases h2 : R k <;> cases h3 : R l <;> simp_all

