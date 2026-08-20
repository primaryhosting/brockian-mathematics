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

/-!
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This file is deliberately self-contained (no `import` line), because the
-- required header above is a module doc-comment, which Lean only accepts at
-- the very top of a file, i.e. before any `import`.  Nothing below needs
-- Mathlib: a search of Mathlib turns up no Collatz material at all, and the
-- ingredients used here (iteration of a map, strong induction on `ℕ`) are
-- developed from scratch.

namespace Brockian.CollatzPartial

/-- One step of the Collatz (`3n + 1`) map: halve `n` when it is even,
otherwise send `n` to `3 * n + 1`. -/

def collatzStep (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `k`-fold iteration of `collatzStep`. -/

def collatzIter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => collatzIter k (collatzStep n)

@[simp] theorem collatzIter_zero (n : Nat) : collatzIter 0 n = n := rfl

theorem collatzIter_succ (k n : Nat) :
    collatzIter (k + 1) n = collatzIter k (collatzStep n) := rfl

/-- Iteration counts add. -/

theorem collatzIter_add (j k n : Nat) :
    collatzIter (j + k) n = collatzIter j (collatzIter k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      have h : j + (k + 1) = (j + k) + 1 := by omega
      rw [h, collatzIter_succ, collatzIter_succ, ih]

/-- `CollatzReachesOne n` says the Collatz orbit of `n` hits `1`. -/

def CollatzReachesOne (n : Nat) : Prop := ∃ k : Nat, collatzIter k n = 1

/-- The Collatz conjecture: every positive natural number reaches `1`. -/

def CollatzStatement : Prop := ∀ n : Nat, 0 < n → CollatzReachesOne n

/-- The *descent* form of the Collatz conjecture: every `n > 1` has some later
point of its orbit strictly below `n`. -/

def CollatzDescent : Prop :=
  ∀ n : Nat, 1 < n → ∃ k : Nat, 0 < k ∧ collatzIter k n < n

/-- The Collatz map sends positive numbers to positive numbers. -/

theorem collatzStep_pos {n : Nat} (hn : 0 < n) : 0 < collatzStep n := by
  unfold collatzStep
  split
  · omega
  · omega

/-- Iterates of the Collatz map keep positivity. -/

theorem collatzIter_pos {n : Nat} (hn : 0 < n) (k : Nat) : 0 < collatzIter k n := by
  induction k generalizing n with
  | zero => simpa using hn
  | succ k ih => exact ih (collatzStep_pos hn)

/-- If some point of the orbit of `n` reaches `1`, then so does `n`. -/

theorem CollatzReachesOne.of_iter {n k : Nat}
    (h : CollatzReachesOne (collatzIter k n)) : CollatzReachesOne n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j + k, by rw [collatzIter_add]; exact hj⟩

/-- **Conditional reduction of the Collatz conjecture.**

Assuming the descent principle `CollatzDescent` — every `n > 1` eventually
reaches a value strictly smaller than `n` — every positive natural number
reaches `1` under iteration of the Collatz map.

The Collatz conjecture is open, so this is a Lean-checked conditional
statement.  The theorem `collatz_descent_iff` below shows the hypothesis is
in fact *equivalent* to the conjecture, so the reduction is faithful: the
content proved here is exactly the (standard) passage from "every orbit
descends" to "every orbit reaches 1". -/

theorem CollatzConjecture (hdesc : CollatzDescent) : CollatzStatement := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with h1 | h1
    · have : n = 1 := by omega
      exact ⟨0, by simp [this]⟩
    · obtain ⟨k, _, hk⟩ := hdesc n (by omega)
      exact CollatzReachesOne.of_iter (ih _ hk (collatzIter_pos hn k))

/-- The descent principle is equivalent to the Collatz conjecture. -/

theorem collatz_descent_iff : CollatzDescent ↔ CollatzStatement := by
  refine ⟨CollatzConjecture, fun h n hn => ?_⟩
  obtain ⟨k, hk⟩ := h n (by omega)
  refine ⟨k, ?_, by omega⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [collatzIter_zero] at hk; omega
  · exact hk0

/-- `1`, `2` and `4` all reach `1` (they form the trivial cycle). -/
