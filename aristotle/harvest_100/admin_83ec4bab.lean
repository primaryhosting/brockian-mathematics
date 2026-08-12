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
def ack : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

@[simp] theorem ack_zero (n : ℕ) : ack 0 n = n + 1 := by rw [ack]

@[simp] theorem ack_succ_zero (m : ℕ) : ack (m + 1) 0 = ack m 1 := by rw [ack]

@[simp] theorem ack_succ_succ (m n : ℕ) :
    ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by rw [ack]

/-- The graph of the Ackermann recursion, given as an inductive relation:
`AckRel m n v` means "`v` is a value obtained from the Ackermann equations at `(m, n)`". -/
inductive AckRel : ℕ → ℕ → ℕ → Prop
  | zero (n : ℕ) : AckRel 0 n (n + 1)
  | succZero {m r : ℕ} : AckRel m 1 r → AckRel (m + 1) 0 r
  | succSucc {m n r s : ℕ} : AckRel (m + 1) n r → AckRel m r s → AckRel (m + 1) (n + 1) s

/-- The lexicographic order on `ℕ × ℕ` used as the termination measure is well-founded. -/
theorem lex_wellFounded :
    WellFounded (Prod.Lex ((· < ·) : ℕ → ℕ → Prop) ((· < ·) : ℕ → ℕ → Prop)) :=
  IsWellFounded.wf

/-- Existence: the Ackermann equations produce a value at every argument.  Proved by
well-founded induction on the lexicographic order on `ℕ × ℕ`. -/
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
theorem AckRel.functional {m n v w : ℕ} (h1 : AckRel m n v) (h2 : AckRel m n w) : v = w := by
  induction h1 generalizing w with
  | zero n => cases h2; rfl
  | succZero _ ih => cases h2 with | succZero h' => exact ih h'
  | succSucc _ _ ih1 ih2 =>
    cases h2 with
    | succSucc k1 k2 =>
      have hr := ih1 k1
      subst hr
      exact ih2 k2

/-- The defined function `ack` satisfies the Ackermann equations. -/
theorem ack_ackRel : ∀ m n : ℕ, AckRel m n (ack m n)
  | 0, n => by simpa using AckRel.zero n
  | m + 1, 0 => by simpa using AckRel.succZero (ack_ackRel m 1)
  | m + 1, n + 1 => by
    simpa using AckRel.succSucc (ack_ackRel (m + 1) n) (ack_ackRel m (ack (m + 1) n))
termination_by m n => (m, n)

/-- **The Ackermann function is total.**  For every pair `(m, n)` of natural numbers there is a
unique value satisfying the Ackermann recursion equations; it is computed by `CS.ack`, which is
defined by well-founded recursion on the lexicographic order on `ℕ × ℕ`. -/
theorem ackermann_total : ∀ m n : ℕ, ∃! v : ℕ, AckRel m n v := by
  intro m n
  exact ⟨ack m n, ack_ackRel m n, fun w hw => hw.functional (ack_ackRel m n)⟩

end CS

