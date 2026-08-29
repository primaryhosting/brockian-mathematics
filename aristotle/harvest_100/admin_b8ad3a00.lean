/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-- The lexicographic order on `Nat × Nat`, the measure used for the Ackermann recursion. -/
abbrev natLex : Nat × Nat → Nat × Nat → Prop := Prod.Lex Nat.lt Nat.lt

/-- The lexicographic order on `Nat × Nat` is well-founded. -/
theorem natLex_wf : WellFounded natLex :=
  WellFounded.intro fun p =>
    Prod.lexAccessible (Nat.lt_wfRel.wf.apply p.1) (fun b => Nat.lt_wfRel.wf.apply b) p.2

/-- The Ackermann function, defined by well-founded recursion on `natLex`. -/
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

@[simp] theorem ack_zero (n : Nat) : ack 0 n = n + 1 := by
  rw [ack]

@[simp] theorem ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1 := by
  rw [ack]

@[simp] theorem ack_succ_succ (m n : Nat) : ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by
  rw [ack]

/-- Each of the three recursive calls in the definition of the Ackermann function
strictly decreases the argument pair in the lexicographic order. -/
theorem ack_recursion_decreasing (m n v : Nat) :
    natLex (m, 1) (m + 1, 0) ∧ natLex (m + 1, n) (m + 1, n + 1) ∧
      natLex (m, v) (m + 1, n + 1) :=
  ⟨Prod.Lex.left _ _ (Nat.lt_succ_self m), Prod.Lex.right _ (Nat.lt_succ_self n),
    Prod.Lex.left _ _ (Nat.lt_succ_self m)⟩

/-- The graph of the Ackermann recursion: `AckGraph m n v` holds when the defining
equations force the value of the Ackermann function at `(m, n)` to be `v`. -/
inductive AckGraph : Nat → Nat → Nat → Prop
  | zero (n : Nat) : AckGraph 0 n (n + 1)
  | succ_zero {m v : Nat} : AckGraph m 1 v → AckGraph (m + 1) 0 v
  | succ_succ {m n v w : Nat} :
      AckGraph (m + 1) n v → AckGraph m v w → AckGraph (m + 1) (n + 1) w

/-- Existence: `ack m n` satisfies the Ackermann recursion at every point. -/
theorem ackGraph_ack : ∀ m n : Nat, AckGraph m n (ack m n) := by
  intro m
  induction m with
  | zero => intro n; simpa using AckGraph.zero n
  | succ m ih =>
    intro n
    induction n with
    | zero => simpa using AckGraph.succ_zero (ih 1)
    | succ n ihn => simpa using AckGraph.succ_succ ihn (ih (ack (m + 1) n))

/-- Uniqueness: any value related to `(m, n)` by the Ackermann recursion equals `ack m n`. -/
theorem ackGraph_eq_ack : ∀ {m n v : Nat}, AckGraph m n v → v = ack m n := by
  intro m n v h
  induction h with
  | zero n => simp
  | succ_zero _ ih => simpa using ih
  | succ_succ _ _ ih₁ ih₂ =>
    subst ih₁
    simpa using ih₂

/--
**The Ackermann function is total.**

The lexicographic order on `Nat × Nat` is well-founded, and with it as termination measure
the Ackermann recursion
`A(0, n) = n + 1`, `A(m+1, 0) = A(m, 1)`, `A(m+1, n+1) = A(m, A(m+1, n))`
determines exactly one value at every pair `(m, n)`: the relation `AckGraph` given by the
three defining equations has a unique solution everywhere, namely `ack m n`.
-/
theorem ackermann_total :
    WellFounded natLex ∧
      ∀ m n : Nat, ∃ v : Nat, AckGraph m n v ∧ ∀ w : Nat, AckGraph m n w → w = v :=
  ⟨natLex_wf, fun m n => ⟨ack m n, ackGraph_ack m n, fun _ h => ackGraph_eq_ack h⟩⟩

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

