/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The Ackermann function, defined by well-founded recursion on the lexicographic
order of `Nat × Nat`. -/
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

@[simp] theorem ack_zero (n : Nat) : ack 0 n = n + 1 := by rw [ack]

@[simp] theorem ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1 := by rw [ack]

@[simp] theorem ack_succ_succ (m n : Nat) :
    ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by rw [ack]

/-- The defining equations of the Ackermann function, presented as an inductively
generated graph: `AckGraph m n v` reads "the Ackermann function maps `(m, n)` to `v`". -/
inductive AckGraph : Nat → Nat → Nat → Prop
  | zero (n : Nat) : AckGraph 0 n (n + 1)
  | succ_zero {m v : Nat} : AckGraph m 1 v → AckGraph (m + 1) 0 v
  | succ_succ {m n u v : Nat} : AckGraph (m + 1) n u → AckGraph m u v →
      AckGraph (m + 1) (n + 1) v

/-- The lexicographic order on `Nat × Nat` that justifies the recursion is well founded. -/
theorem lex_wellFounded :
    WellFounded (Prod.Lex (· < · : Nat → Nat → Prop) (· < · : Nat → Nat → Prop)) :=
  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-- Existence: for every input pair, `ack` produces a value satisfying the equations. -/
theorem ackGraph_ack : ∀ m n : Nat, AckGraph m n (ack m n)
  | 0, n => by simpa using AckGraph.zero n
  | m + 1, 0 => by
      simpa using AckGraph.succ_zero (ackGraph_ack m 1)
  | m + 1, n + 1 => by
      have h₁ := ackGraph_ack (m + 1) n
      have h₂ := ackGraph_ack m (ack (m + 1) n)
      simpa using AckGraph.succ_succ h₁ h₂
termination_by m n => (m, n)

/-- Uniqueness: the graph of the Ackermann equations is functional. -/
theorem ackGraph_unique {m n v : Nat} (h : AckGraph m n v) : v = ack m n := by
  induction h with
  | zero n => simp
  | succ_zero _ ih => simpa using ih
  | succ_succ _ _ ih₁ ih₂ => subst ih₁; simpa using ih₂

/--
**The Ackermann function is total.**

Its recursion is justified by the well-founded lexicographic order on `Nat × Nat`, and
for every input pair `(m, n)` there is exactly one value `v` satisfying the Ackermann
equations (encoded by the graph `AckGraph`), namely `ack m n`.
-/
theorem ackermann_total :
    WellFounded (Prod.Lex (· < · : Nat → Nat → Prop) (· < · : Nat → Nat → Prop)) ∧
      ∀ m n : Nat, ∃ v : Nat, AckGraph m n v ∧ ∀ w : Nat, AckGraph m n w → w = v :=
  ⟨lex_wellFounded, fun m n =>
    ⟨ack m n, ackGraph_ack m n, fun _ hw => ackGraph_unique hw⟩⟩

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

