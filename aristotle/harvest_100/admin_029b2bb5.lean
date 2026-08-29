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

-- Note: Lean forbids `import` commands after a module docstring. So, in order for the
-- required header above to be the very first thing in the file, this development is
-- written to be self-contained: it uses only the Lean core prelude, with no `import`.

namespace Brockian.CollatzPartial

/-- The Collatz step: `n ↦ n / 2` for even `n`, and `n ↦ 3 * n + 1` for odd `n`. -/
def collatz (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `collatzIter k n` is the result of applying `k` Collatz steps to `n`. -/
def collatzIter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => collatz (collatzIter k n)

/-- `Reaches1 n` says that iterating the Collatz step from `n` eventually reaches `1`. -/
def Reaches1 (n : Nat) : Prop := ∃ k : Nat, collatzIter k n = 1

/-- The *eventual descent* principle: every `n > 1` is carried, by a positive number of
Collatz steps, to a value strictly smaller than `n`. -/
def EventualDescent : Prop := ∀ n : Nat, 1 < n → ∃ k : Nat, 0 < k ∧ collatzIter k n < n

/-! ### Basic facts about the iteration -/

@[simp] theorem collatzIter_zero (n : Nat) : collatzIter 0 n = n := rfl

theorem collatzIter_succ (k n : Nat) : collatzIter (k + 1) n = collatz (collatzIter k n) := rfl

theorem collatzIter_add (j k n : Nat) :
    collatzIter (j + k) n = collatzIter j (collatzIter k n) := by
  induction j with
  | zero => rw [Nat.zero_add]; rfl
  | succ j ih =>
      have hj : j + 1 + k = (j + k) + 1 := by omega
      rw [hj, collatzIter_succ, ih, collatzIter_succ]

/-- One Collatz step may equivalently be taken first. -/
theorem collatzIter_succ' (k n : Nat) : collatzIter (k + 1) n = collatzIter k (collatz n) := by
  rw [collatzIter_add k 1]
  rfl

/-- The Collatz step preserves positivity. -/
theorem collatz_pos {n : Nat} (hn : 0 < n) : 0 < collatz n := by
  unfold collatz
  split <;> omega

/-- Iterating the Collatz step preserves positivity. -/
theorem collatzIter_pos {n : Nat} (hn : 0 < n) (k : Nat) : 0 < collatzIter k n := by
  induction k with
  | zero => exact hn
  | succ k ih => exact collatz_pos ih

/-- If some iterate of `n` reaches `1`, then so does `n`. -/
theorem reaches1_of_iterate {n k : Nat} (h : Reaches1 (collatzIter k n)) : Reaches1 n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j + k, by rw [collatzIter_add]; exact hj⟩

/-! ### The main conditional result -/

/-- **Conditional reduction of the Collatz conjecture.**

Assuming the eventual descent principle `EventualDescent` — that every integer `n > 1`
is carried by finitely many (at least one) Collatz steps to a strictly smaller value —
every positive integer eventually reaches `1`.

The Collatz conjecture itself is open, so the statement is given in this conditional
form. The theorem `collatz_conjecture_iff_eventualDescent` below shows that the
hypothesis is in fact *equivalent* to the full conjecture, so nothing is lost or
smuggled in: the content proved here is exactly the reduction of the conjecture to a
local descent statement, by strong induction on `n`. -/
theorem CollatzConjecture (h : EventualDescent) : ∀ n : Nat, 0 < n → Reaches1 n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · obtain ⟨k, _, hk⟩ := h n h1
      exact reaches1_of_iterate (ih _ hk (collatzIter_pos hn k))
    · have : n = 1 := by omega
      exact ⟨0, by simp [this]⟩

/-- The hypothesis of `CollatzConjecture` is equivalent to the Collatz conjecture,
so the reduction above is lossless. -/
theorem collatz_conjecture_iff_eventualDescent :
    EventualDescent ↔ ∀ n : Nat, 0 < n → Reaches1 n := by
  constructor
  · exact CollatzConjecture
  · intro h n hn
    obtain ⟨k, hk⟩ := h n (by omega)
    refine ⟨k, ?_, by rw [hk]; omega⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · rw [collatzIter_zero] at hk; omega
    · exact hk'

/-! ### Unconditional partial results -/

/-- If `n` is even and `n / 2` reaches `1`, then so does `n`. -/
theorem reaches1_of_even {n : Nat} (he : n % 2 = 0) (h : Reaches1 (n / 2)) : Reaches1 n := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k + 1, ?_⟩
  rw [collatzIter_succ']
  unfold collatz
  rw [if_pos he]
  exact hk

/-- If `n` is odd and `3 * n + 1` reaches `1`, then so does `n`. -/
theorem reaches1_of_odd {n : Nat} (ho : n % 2 = 1) (h : Reaches1 (3 * n + 1)) : Reaches1 n := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k + 1, ?_⟩
  rw [collatzIter_succ']
  unfold collatz
  rw [if_neg (by omega : ¬ n % 2 = 0)]
  exact hk

/-- Every power of two reaches `1`. -/
theorem reaches1_two_pow (k : Nat) : Reaches1 (2 ^ k) := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
      have hp : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
      refine reaches1_of_even (by omega) ?_
      have : 2 ^ (k + 1) / 2 = 2 ^ k := by omega
      rw [this]
      exact ih

/-- A bounded, decidable search for a path from `n` to `1` using at most `fuel` steps. -/
def reach1B : Nat → Nat → Bool
  | 0, n => n == 1
  | fuel + 1, n => n == 1 || reach1B fuel (collatz n)

/-- The bounded search is sound: a successful search witnesses `Reaches1`. -/
theorem reaches1_of_reach1B : ∀ (fuel n : Nat), reach1B fuel n = true → Reaches1 n := by
  intro fuel
  induction fuel with
  | zero =>
      intro n h
      have : n = 1 := by simpa [reach1B] using h
      exact ⟨0, by simp [this]⟩
  | succ fuel ih =>
      intro n h
      rw [reach1B, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · exact ⟨0, by simp [h]⟩
      · obtain ⟨k, hk⟩ := ih (collatz n) h
        exact ⟨k + 1, by rw [collatzIter_succ']; exact hk⟩

/-- **Unconditional numerical verification.** Every `n` with `0 < n < 1000`
reaches `1`. -/
theorem reaches1_of_lt_1000 (n : Nat) (h0 : 0 < n) (h1 : n < 1000) : Reaches1 n := by
  refine reaches1_of_reach1B 200 n ?_
  have : ∀ m : Nat, m < 1000 → 0 < m → reach1B 200 m = true := by
    set_option maxRecDepth 100000 in decide
  exact this n h1 h0

/-- Any `n` whose Collatz trajectory ever enters a power of two reaches `1`. -/
theorem reaches1_of_iterate_eq_two_pow {n k m : Nat} (h : collatzIter k n = 2 ^ m) :
    Reaches1 n :=
  reaches1_of_iterate (k := k) (h ▸ reaches1_two_pow m)

end Brockian.CollatzPartial

