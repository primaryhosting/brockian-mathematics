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

theorem tseitin_sat_iff (p : List Gate) :
    Satisfiable (tseitin p) ↔ ∃ x : ℕ → Bool, evalProg p x = true := by
  constructor
  · rintro ⟨a, ha⟩
    simp only [cnfEval, List.all_eq_true] at ha
    have hzero : a 0 = false := by
      have h := ha [(0, false)] (by simp [tseitin])
      simpa [clauseEval, litEval] using h
    have hne : p ≠ [] := by
      intro h
      subst h
      have h2 := ha [] (by simp [tseitin])
      simp [clauseEval] at h2
    refine ⟨fun i => a (xvar i), ?_⟩
    have key : ∀ j, j < p.length → a (gvar j) = (vals p (fun i => a (xvar i))).getD j false := by
      intro j
      induction j using Nat.strong_induction_on with
      | _ j ih =>
        intro hj
        have hR2 : ∀ k, j ≤ k →
            (vals (p.take j) (fun i => a (xvar i))).getD k false = false := by
          intro k hk
          rw [vals_take_getD p _ (le_of_lt hj) k, if_neg (by omega)]
        have hR1 : ∀ k, k < j →
            a (gvar k) = (vals (p.take j) (fun i => a (xvar i))).getD k false := by
          intro k hk
          rw [vals_take_getD p _ (le_of_lt hj) k, if_pos hk]
          exact ih k hk (by omega)
        have hgc : ∀ c ∈ gateClauses j (p.getD j (.cst false)), clauseEval a c = true :=
          fun c hc => ha c (mem_tseitin_of_gateClauses p j hj c hc)
        have hmain := (gateClauses_true_iff a j (p.getD j (.cst false)) (fun i => a (xvar i))
          (fun k => (vals (p.take j) (fun i => a (xvar i))).getD k false) (fun _ => rfl)
          (refLit_eval_true a j _ hzero hR1 hR2) (refLit_eval_false a j _ hzero hR1 hR2)).1 hgc
        rw [vals_getD_step p _ hj, gateVal_eq_gateValR]
        exact hmain
    have hout := ha [(gvar (p.length - 1), true)] (by simp [tseitin])
    have h2 : a (gvar (p.length - 1)) = true := by
      simpa [clauseEval, litEval] using hout
    have hlen : p.length - 1 < p.length := by
      have : 0 < p.length := List.length_pos_iff.2 hne
      omega
    rw [evalProg, ← key _ hlen]
    exact h2
  · rintro ⟨x, hx⟩
    have hne : p ≠ [] := by
      intro h
      subst h
      simp [evalProg, vals, evalAux] at hx
    refine ⟨tseitinAssign p x, ?_⟩
    simp only [cnfEval, List.all_eq_true]
    intro c hc
    simp only [tseitin, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range] at hc
    rcases hc with rfl | rfl | hc | ⟨j, hj, hjc⟩
    · simp [clauseEval, litEval, tseitinAssign_zero]
    · have : tseitinAssign p x (gvar (p.length - 1)) = true := by
        rw [tseitinAssign_gvar]
        exact hx
      simp [clauseEval, litEval, this]
    · rw [if_neg (by simp [List.isEmpty_iff, hne])] at hc
      simp at hc
    · have hR2 : ∀ k, j ≤ k → (vals (p.take j) x).getD k false = false := by
        intro k hk
        rw [vals_take_getD p x (le_of_lt hj) k, if_neg (by omega)]
      have hR1 : ∀ k, k < j → tseitinAssign p x (gvar k) = (vals (p.take j) x).getD k false := by
        intro k hk
        rw [tseitinAssign_gvar, vals_take_getD p x (le_of_lt hj) k, if_pos hk]
      refine (gateClauses_true_iff (tseitinAssign p x) j (p.getD j (.cst false)) x
        (fun k => (vals (p.take j) x).getD k false) (tseitinAssign_xvar p x)
        (refLit_eval_true _ j _ (tseitinAssign_zero p x) hR1 hR2)
        (refLit_eval_false _ j _ (tseitinAssign_zero p x) hR1 hR2)).2 ?_ c hjc
      rw [tseitinAssign_gvar, vals_getD_step p x hj, gateVal_eq_gateValR]

