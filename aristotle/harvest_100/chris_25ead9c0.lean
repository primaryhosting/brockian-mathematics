/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The lexicographic order on `Nat × Nat`, used as the termination measure for the Ackermann
recursion. -/
def LexNat : Nat × Nat → Nat × Nat → Prop :=
  Prod.Lex (· < ·) (· < ·)

/-- The lexicographic order on `Nat × Nat` is well-founded. -/
theorem lexNat_wf : WellFounded LexNat :=
  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-- The recursive call `A m 1` made by `A (m+1) 0` decreases in the lexicographic order. -/
theorem lexNat_succZero (m : Nat) : LexNat (m, 1) (m + 1, 0) :=
  Prod.Lex.left _ _ (Nat.lt_succ_self m)

/-- The outer recursive call `A (m+1) n` made by `A (m+1) (n+1)` decreases lexicographically. -/
theorem lexNat_succSucc_outer (m n : Nat) : LexNat (m + 1, n) (m + 1, n + 1) :=
  Prod.Lex.right _ (Nat.lt_succ_self n)

/-- The inner recursive call `A m v` made by `A (m+1) (n+1)` decreases lexicographically,
whatever the value `v` computed by the outer call. -/
theorem lexNat_succSucc_inner (m n v : Nat) : LexNat (m, v) (m + 1, n + 1) :=
  Prod.Lex.left _ _ (Nat.lt_succ_self m)

/-- The two-argument Ackermann function, defined by well-founded recursion on the pair of its
arguments ordered lexicographically. -/
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

@[simp] theorem ack_zero (n : Nat) : ack 0 n = n + 1 := by rw [ack]

@[simp] theorem ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1 := by rw [ack]

@[simp] theorem ack_succ_succ (m n : Nat) : ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by
  rw [ack]

/-- The *graph* (input/output relation) of the Ackermann recursion, given by its three defining
equations, without presupposing that a total function satisfying them exists. -/
inductive AckGraph : Nat → Nat → Nat → Prop
  /-- `A 0 n = n + 1`. -/
  | zero (n : Nat) : AckGraph 0 n (n + 1)
  /-- `A (m+1) 0 = A m 1`. -/
  | succZero {m v : Nat} : AckGraph m 1 v → AckGraph (m + 1) 0 v
  /-- `A (m+1) (n+1) = A m (A (m+1) n)`. -/
  | succSucc {m n v w : Nat} : AckGraph (m + 1) n v → AckGraph m v w → AckGraph (m + 1) (n + 1) w

/-- Existence: the function `ack` satisfies the Ackermann recursion at every input. -/
theorem ackGraph_ack (m n : Nat) : AckGraph m n (ack m n) := by
  induction m generalizing n with
  | zero => simpa using AckGraph.zero n
  | succ m ihm =>
    induction n with
    | zero => simpa using AckGraph.succZero (ihm 1)
    | succ n ihn => simpa using AckGraph.succSucc ihn (ihm (ack (m + 1) n))

/-- Uniqueness: any value related to `(m, n)` by the Ackermann recursion equals `ack m n`. -/
theorem eq_ack_of_ackGraph {m n v : Nat} (h : AckGraph m n v) : v = ack m n := by
  induction h with
  | zero n => simp
  | succZero _ ih => simpa using ih
  | succSucc _ _ ih₁ ih₂ => subst ih₁; simpa using ih₂

/-- **The Ackermann function is total.**

The Ackermann recursion, whose recursive calls all decrease in the (well-founded, see
`CS.lexNat_wf`) lexicographic order on `Nat × Nat`, determines exactly one output value for every
pair of inputs: for all `m n : Nat` there is a unique `v` with `AckGraph m n v`. -/
theorem ackermann_total :
    ∀ m n : Nat, ∃ v : Nat, AckGraph m n v ∧ ∀ w : Nat, AckGraph m n w → w = v := fun m n =>
  ⟨ack m n, ackGraph_ack m n, fun _ h => eq_ack_of_ackGraph h⟩

/-- The unique output determined by the Ackermann recursion at `(m, n)` is `ack m n`. -/
theorem ackGraph_iff {m n v : Nat} : AckGraph m n v ↔ v = ack m n :=
  ⟨eq_ack_of_ackGraph, fun h => h ▸ ackGraph_ack m n⟩

end CS

#print axioms CS.ackermann_total

import Mathlib.Computability.Ackermann
import RequestProject.AckermannTotal

/-!
# Ackermann Total — Mathlib-facing restatement

The main development lives in `RequestProject/AckermannTotal.lean`, whose target theorem
`CS.ackermann_total` is stated over core `Nat` (that file must begin with a fixed header comment,
and Lean requires `import` lines to precede every other token, so it carries no imports).

Here we restate totality with Mathlib's `∃!` and `ℕ` notation, and identify the function
`CS.ack` constructed there with Mathlib's `_root_.ack`.
-/

namespace CS

/-- The Ackermann function defined here by well-founded recursion on the lexicographic order
agrees with Mathlib's `ack`. -/
theorem cs_ack_eq_ack (m n : ℕ) : CS.ack m n = _root_.ack m n := by
  induction m generalizing n with
  | zero => simp
  | succ m ihm =>
    induction n with
    | zero =>
      rw [CS.ack_succ_zero, _root_.ack_succ_zero]
      exact ihm 1
    | succ n ihn =>
      rw [CS.ack_succ_succ, _root_.ack_succ_succ, ihn]
      exact ihm _

/-- Mathlib's `ack` satisfies the Ackermann recursion. -/
theorem ackGraph_mathlib_ack (m n : ℕ) : AckGraph m n (_root_.ack m n) := by
  rw [← cs_ack_eq_ack]
  exact ackGraph_ack m n

/-- **The Ackermann function is total**, stated with `∃!`: for all `m n : ℕ` there is a unique
value `v` related to `(m, n)` by the Ackermann recursion, namely `ack m n`. -/
theorem ackermann_total_existsUnique (m n : ℕ) : ∃! v : ℕ, AckGraph m n v :=
  ⟨_root_.ack m n, ackGraph_mathlib_ack m n,
    fun _ h => (eq_ack_of_ackGraph h).trans (cs_ack_eq_ack m n)⟩

/-- Sanity check: the value determined by the recursion at `(2, 5)` is `13`. -/
example : ∃! v : ℕ, AckGraph 2 5 v := by
  refine ⟨13, ?_, fun w hw => ?_⟩
  · have : (13 : ℕ) = _root_.ack 2 5 := by simp
    rw [this]
    exact ackGraph_mathlib_ack 2 5
  · rw [eq_ack_of_ackGraph hw, cs_ack_eq_ack]
    simp

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

