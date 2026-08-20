/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-- The lexicographic order on `Nat × Nat` is well founded.  This is the termination
measure that justifies the recursive definition of the Ackermann function.  It follows
from the existing library lemma `Prod.lexAccessible` together with the well-foundedness
of `<` on `Nat` (`Nat.lt_wfRel`). -/
theorem lex_nat_nat_wellFounded :
    WellFounded (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)) :=
  ⟨fun p => Prod.lexAccessible (Nat.lt_wfRel.wf.apply p.1) Nat.lt_wfRel.wf.apply p.2⟩

/-- The Ackermann function, defined by well-founded recursion on the lexicographic
order of `Nat × Nat`. -/
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
  termination_by m n => (m, n)

@[simp] theorem ack_zero (n : Nat) : ack 0 n = n + 1 := by rw [ack]

@[simp] theorem ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1 := by rw [ack]

@[simp] theorem ack_succ_succ (m n : Nat) : ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by
  rw [ack]

/-- The graph of the Ackermann function: `AckGraph m n v` means that the defining
equations of the Ackermann function force the value at `(m, n)` to be `v`. -/
inductive AckGraph : Nat → Nat → Nat → Prop
  | zero (n : Nat) : AckGraph 0 n (n + 1)
  | succZero {m v : Nat} : AckGraph m 1 v → AckGraph (m + 1) 0 v
  | succSucc {m n v w : Nat} :
      AckGraph (m + 1) n v → AckGraph m v w → AckGraph (m + 1) (n + 1) w

/-- Existence: `ack` satisfies the Ackermann recurrences at every point.  The recursion is
justified by the lexicographic well-founded order on `Nat × Nat`. -/
theorem ackGraph_ack : ∀ m n : Nat, AckGraph m n (ack m n)
  | 0, n => by rw [ack_zero]; exact AckGraph.zero n
  | m + 1, 0 => by
      rw [ack_succ_zero]
      exact AckGraph.succZero (ackGraph_ack m 1)
  | m + 1, n + 1 => by
      rw [ack_succ_succ]
      exact AckGraph.succSucc (ackGraph_ack (m + 1) n) (ackGraph_ack m (ack (m + 1) n))
  termination_by m n => (m, n)

/-- Uniqueness: the Ackermann equations determine at most one value at each point. -/
theorem ackGraph_eq_ack {m n v : Nat} (h : AckGraph m n v) : v = ack m n := by
  induction h with
  | zero n => rw [ack_zero]
  | succZero _ ih => rw [ack_succ_zero]; exact ih
  | succSucc _ _ ih₁ ih₂ => subst ih₁; rw [ack_succ_succ]; exact ih₂

/-- **The Ackermann function is total.**  For every pair `(m, n)` of naturals there is a
(unique) value satisfying the Ackermann recurrences

* `A 0 n = n + 1`,
* `A (m+1) 0 = A m 1`,
* `A (m+1) (n+1) = A m (A (m+1) n)`.

The recursion terminates because the lexicographic order on `Nat × Nat` is well founded
(`lex_nat_nat_wellFounded`), and `ack` is the total function realising it. -/
theorem ackermann_total :
    ∀ m n : Nat, ∃ v : Nat, AckGraph m n v ∧ ∀ w : Nat, AckGraph m n w → w = v :=
  fun m n => ⟨ack m n, ackGraph_ack m n, fun _ hw => ackGraph_eq_ack hw⟩

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

import Mathlib
import RequestProject.AckermannTotal

/-!
# Ackermann Total — Mathlib bridge

`RequestProject/AckermannTotal.lean` must literally begin with the prescribed header
comment, which forces it to be import-free (Lean does not allow a module docstring
before `import`).  This file connects that development with Mathlib: it identifies
`CS.ack` with Mathlib's `ack` and restates totality using Mathlib's `∃!` notation.
-/

namespace CS

/-- Our `ack` agrees with Mathlib's `ack`. -/
theorem ack_eq_nat_ack : ∀ m n : ℕ, ack m n = _root_.ack m n
  | 0, n => by rw [ack_zero, _root_.ack_zero]
  | m + 1, 0 => by rw [ack_succ_zero, _root_.ack_succ_zero, ack_eq_nat_ack m 1]
  | m + 1, n + 1 => by
      rw [ack_succ_succ, _root_.ack_succ_succ, ack_eq_nat_ack (m + 1) n,
        ack_eq_nat_ack m (_root_.ack (m + 1) n)]
  termination_by m n => (m, n)

/-- Totality of the Ackermann function, stated with Mathlib's `∃!`. -/
theorem ackermann_total' (m n : ℕ) : ∃! v : ℕ, AckGraph m n v :=
  ⟨ack m n, ackGraph_ack m n, fun _ hw => ackGraph_eq_ack hw⟩

end CS

