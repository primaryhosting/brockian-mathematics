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

namespace CS

/-- The Ackermann function, defined by well-founded recursion on the
lexicographic order on `ℕ × ℕ`. -/

theorem exists_ackRel (p : ℕ × ℕ) : ∃ v, AckRel p.1 p.2 v := by
  induction p using WellFounded.induction
    (r := Prod.Lex ((· < ·) : ℕ → ℕ → Prop) ((· < ·) : ℕ → ℕ → Prop)) lex_wellFounded with
  | _ p ih =>
    obtain ⟨m, n⟩ := p
    match m, n with
    | 0, n => exact ⟨n + 1, AckRel.zero n⟩
    | m + 1, 0 =>
      obtain ⟨r, hr⟩ := ih (m, 1) (Prod.Lex.left _ _ (Nat.lt_succ_self m))
      exact ⟨r, AckRel.succZero hr⟩
    | m + 1, n + 1 =>
      obtain ⟨r, hr⟩ := ih (m + 1, n) (Prod.Lex.right _ (Nat.lt_succ_self n))
      obtain ⟨s, hs⟩ := ih (m, r) (Prod.Lex.left _ _ (Nat.lt_succ_self m))
      exact ⟨s, AckRel.succSucc hr hs⟩

/-- Uniqueness: the Ackermann equations are deterministic. -/
