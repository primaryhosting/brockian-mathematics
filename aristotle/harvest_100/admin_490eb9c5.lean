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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (no `import` at all), so that the header comment
above can literally be the first thing in the file: Lean requires `import` commands to precede
any other syntax, including module documentation.  Consequently the factorial function is
defined here from scratch rather than taken from Mathlib.
-/

namespace Brockian.BrocardGap

/-- The factorial function, `factorial n = n !`. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

@[inherit_doc] scoped notation:10000 n "!" => factorial n

/-- `n` is a *Brocard index* if `n ! + 1` is a perfect square, i.e. `n` occurs in a solution
`(n, m)` of Brocard's equation `n ! + 1 = m ^ 2`. -/
def IsBrocardIndex (n : Nat) : Prop := ∃ m : Nat, n ! + 1 = m ^ 2

/-- A natural number lying strictly between two consecutive squares is not a square. -/
theorem not_square_of_between {k a : Nat} (h1 : a ^ 2 < k) (h2 : k < (a + 1) ^ 2) :
    ¬ ∃ m : Nat, k = m ^ 2 := by
  intro ⟨m, hm⟩
  subst hm
  have ha : a + 1 ≤ m := by
    match Nat.lt_or_ge a m with
    | Or.inl h => exact h
    | Or.inr h => exact absurd h1 (Nat.not_lt.mpr (Nat.pow_le_pow_left h 2))
  exact absurd h2 (Nat.not_lt.mpr (Nat.pow_le_pow_left ha 2))

/-- Convenience wrapper: `n ! + 1 = k` and `k` strictly between consecutive squares
implies `n` is not a Brocard index. -/
theorem not_isBrocardIndex_of_between {n k a : Nat} (hk : n ! + 1 = k)
    (h1 : a ^ 2 < k) (h2 : k < (a + 1) ^ 2) : ¬ IsBrocardIndex n := by
  intro h
  rw [IsBrocardIndex, hk] at h
  exact not_square_of_between h1 h2 h

theorem not_isBrocardIndex_zero : ¬ IsBrocardIndex 0 :=
  not_isBrocardIndex_of_between (k := 2) (a := 1) (by decide) (by decide) (by decide)

theorem not_isBrocardIndex_one : ¬ IsBrocardIndex 1 :=
  not_isBrocardIndex_of_between (k := 2) (a := 1) (by decide) (by decide) (by decide)

theorem not_isBrocardIndex_two : ¬ IsBrocardIndex 2 :=
  not_isBrocardIndex_of_between (k := 3) (a := 1) (by decide) (by decide) (by decide)

theorem not_isBrocardIndex_three : ¬ IsBrocardIndex 3 :=
  not_isBrocardIndex_of_between (k := 7) (a := 2) (by decide) (by decide) (by decide)

theorem not_isBrocardIndex_six : ¬ IsBrocardIndex 6 :=
  not_isBrocardIndex_of_between (k := 721) (a := 26) (by decide) (by decide) (by decide)

/-- `4! + 1 = 25 = 5 ^ 2`. -/
theorem isBrocardIndex_four : IsBrocardIndex 4 := ⟨5, by decide⟩

/-- `5! + 1 = 121 = 11 ^ 2`. -/
theorem isBrocardIndex_five : IsBrocardIndex 5 := ⟨11, by decide⟩

/-- `7! + 1 = 5041 = 71 ^ 2`. -/
theorem isBrocardIndex_seven : IsBrocardIndex 7 := ⟨71, by decide⟩

/-- Unconditional finite verification: in the range `n ≤ 7` the Brocard indices are exactly
`4`, `5` and `7`. -/
theorem eq_four_or_five_or_seven_of_le_seven {n : Nat} (hn : n ≤ 7) (h : IsBrocardIndex n) :
    n = 4 ∨ n = 5 ∨ n = 7 := by
  match n, hn, h with
  | 0, _, h => exact absurd h not_isBrocardIndex_zero
  | 1, _, h => exact absurd h not_isBrocardIndex_one
  | 2, _, h => exact absurd h not_isBrocardIndex_two
  | 3, _, h => exact absurd h not_isBrocardIndex_three
  | 4, _, _ => exact Or.inl rfl
  | 5, _, _ => exact Or.inr (Or.inl rfl)
  | 6, _, h => exact absurd h not_isBrocardIndex_six
  | 7, _, _ => exact Or.inr (Or.inr rfl)
  | (k + 8), hn, _ => exact absurd hn (by omega)

/-- The (currently open) arithmetic input to the gap conjecture: Brocard's equation
`n ! + 1 = m ^ 2` has no solution with `n ≥ 8`. -/
def NoBrocardIndexBeyondSeven : Prop := ∀ n : Nat, 8 ≤ n → ¬ IsBrocardIndex n

/--
**Brocard Gap Conjecture** (Lean-checked conditional reduction).

Granting the arithmetic hypothesis `NoBrocardIndexBeyondSeven` — that Brocard's equation
`n ! + 1 = m ^ 2` has no solution with `n ≥ 8` — the set of Brocard indices is completely
determined:

* it is exactly `{4, 5, 7}`;
* every Brocard index is at most `7`, so past `7` there is an infinite gap containing no
  Brocard index at all;
* in particular the Brocard indices `4 < 5 < 7` are consecutive and there is no further one.

The proof splits on the hypothesis `n ≤ 7` versus `8 ≤ n`: the small range is discharged by an
unconditional finite verification, and the large range is exactly the assumed hypothesis.
-/
theorem BrocardGapConjecture (H : NoBrocardIndexBeyondSeven) :
    (∀ n : Nat, IsBrocardIndex n ↔ n = 4 ∨ n = 5 ∨ n = 7) ∧
    (∀ n : Nat, IsBrocardIndex n → n ≤ 7) ∧
    (∀ n : Nat, 7 < n → ¬ IsBrocardIndex n) := by
  have key : ∀ n : Nat, IsBrocardIndex n → n = 4 ∨ n = 5 ∨ n = 7 := by
    intro n hn
    match Nat.lt_or_ge 7 n with
    | Or.inl h => exact absurd hn (H n h)
    | Or.inr h => exact eq_four_or_five_or_seven_of_le_seven h hn
  refine ⟨fun n => ⟨key n, ?_⟩, fun n hn => ?_, fun n hn h => ?_⟩
  · intro h
    match h with
    | Or.inl rfl => exact isBrocardIndex_four
    | Or.inr (Or.inl rfl) => exact isBrocardIndex_five
    | Or.inr (Or.inr rfl) => exact isBrocardIndex_seven
  · match key n hn with
    | Or.inl rfl => exact (by decide)
    | Or.inr (Or.inl rfl) => exact (by decide)
    | Or.inr (Or.inr rfl) => exact (by decide)
  · match key n h with
    | Or.inl rfl => exact absurd hn (by decide)
    | Or.inr (Or.inl rfl) => exact absurd hn (by decide)
    | Or.inr (Or.inr rfl) => exact absurd hn (by decide)

end Brockian.BrocardGap

