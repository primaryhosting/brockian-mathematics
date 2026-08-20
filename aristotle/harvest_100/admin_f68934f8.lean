/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The lexicographic order on `ℕ × ℕ` is well-founded.  This is the order that
justifies the (non-structural) Ackermann recursion: each recursive call either
decreases the first component, or keeps it fixed and decreases the second. -/
theorem lex_nat_wf :
    WellFounded (Prod.Lex (· < ·) (· < ·) : Nat × Nat → Nat × Nat → Prop) :=
  ⟨fun (a, b) => Prod.lexAccessible (Nat.lt_wfRel.wf.apply a)
    (fun b => Nat.lt_wfRel.wf.apply b) b⟩

/-- The Ackermann function, defined by well-founded recursion on the
lexicographic order on `ℕ × ℕ`. -/
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

@[simp] theorem ack_zero (n : Nat) : ack 0 n = n + 1 := by rw [ack]

@[simp] theorem ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1 := by rw [ack]

@[simp] theorem ack_succ_succ (m n : Nat) :
    ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by rw [ack]

/-- The graph of the Ackermann function, as an inductively defined relation:
`Ack m n v` holds exactly when the defining equations of the Ackermann function
derive the value `v` from the arguments `m` and `n`.  This relation is defined
without reference to any purported function, so proving that it relates each
pair `(m, n)` to exactly one value is precisely the statement that the
Ackermann recursion defines a total function. -/
inductive Ack : Nat → Nat → Nat → Prop
  | zero (n : Nat) : Ack 0 n (n + 1)
  | succ_zero {m r : Nat} : Ack m 1 r → Ack (m + 1) 0 r
  | succ_succ {m n r s : Nat} : Ack (m + 1) n r → Ack m r s → Ack (m + 1) (n + 1) s

/-- Existence: `ack m n` is a value related to `(m, n)` by the graph relation. -/
theorem ack_spec (m n : Nat) : Ack m n (ack m n) := by
  induction m, n using ack.induct with
  | case1 n => simpa using Ack.zero n
  | case2 m ih => exact Ack.succ_zero (by simpa using ih)
  | case3 m n ih₁ ih₂ => exact Ack.succ_succ ih₁ (by simpa using ih₂)

/-- Uniqueness: any value related to `(m, n)` by the graph relation equals
`ack m n`. -/
theorem Ack.eq_ack {m n v : Nat} (h : Ack m n v) : v = ack m n := by
  induction h with
  | zero n => simp
  | succ_zero _ ih => simpa using ih
  | succ_succ _ _ ih₁ ih₂ => subst ih₁; simpa using ih₂

/-- **The Ackermann function is total.**  For every pair of natural numbers
`(m, n)` the Ackermann recursion equations (encoded by the graph relation
`CS.Ack`) determine exactly one value: there exists a value `v` with
`Ack m n v`, and any `w` with `Ack m n w` equals `v`.  Well-foundedness of the
lexicographic order on `ℕ × ℕ` (`CS.lex_nat_wf`) is what makes the defining
recursion legitimate. -/
theorem ackermann_total :
    ∀ m n : Nat, ∃ v : Nat, Ack m n v ∧ ∀ w : Nat, Ack m n w → w = v :=
  fun m n => ⟨ack m n, ack_spec m n, fun _ hv => hv.eq_ack⟩

end CS

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

