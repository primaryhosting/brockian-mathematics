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

/-
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BrocardGap

open Nat

/-- `n` is a *Brocard number* if `n ! + 1` is a perfect square.
The known Brocard numbers are `4`, `5` and `7` (Brown numbers `(4,5)`, `(5,11)`, `(7,71)`). -/
def IsBrocard (n : ℕ) : Prop := ∃ m : ℕ, n ! + 1 = m ^ 2

/-- A natural number strictly between two consecutive squares is not a square. -/
theorem not_square_of_between {a k : ℕ} (h1 : k ^ 2 < a) (h2 : a < (k + 1) ^ 2) (m : ℕ) :
    a ≠ m ^ 2 := by
  rintro rfl
  have hk : k < m := by nlinarith
  have hm : m < k + 1 := by nlinarith
  omega

/-- Sandwiching `n ! + 1` between two consecutive squares certifies that `n` is not a
Brocard number. -/
theorem not_brocard_of_bounds (n k : ℕ) (h1 : k ^ 2 < n ! + 1) (h2 : n ! + 1 < (k + 1) ^ 2) :
    ¬ IsBrocard n := by
  rintro ⟨m, hm⟩
  exact not_square_of_between h1 h2 m hm

/-- **Reduction to pronic numbers.** For `n ≥ 2`, `n ! + 1` is a perfect square if and only if
`n !` is four times a product of two consecutive integers (i.e. `n !/4` is a pronic number). -/
theorem isBrocard_iff_pronic (n : ℕ) (hn : 2 ≤ n) :
    IsBrocard n ↔ ∃ u : ℕ, n ! = 4 * u * (u + 1) := by
  have hfac : 2 ∣ n ! := Nat.dvd_factorial (by norm_num) hn
  constructor
  · rintro ⟨m, hm⟩
    have hodd : Odd (m ^ 2) := by
      rw [← hm]
      exact Even.add_one ((even_iff_two_dvd).2 hfac)
    have hm' : Odd m := Nat.Odd.of_mul_right hodd
    obtain ⟨u, hu⟩ := hm'
    refine ⟨u, ?_⟩
    have h2 : n ! + 1 = 4 * u * (u + 1) + 1 := by rw [hm, hu]; ring
    exact Nat.add_right_cancel h2
  · rintro ⟨u, hu⟩
    exact ⟨2 * u + 1, by rw [hu]; ring⟩

/-- **Unconditional verification of the initial range.** For every `n ≤ 50`, the number `n ! + 1`
is a perfect square exactly when `n ∈ {4, 5, 7}`. -/
theorem isBrocard_iff_of_le_50 (n : ℕ) (hn : n ≤ 50) : IsBrocard n ↔ (n = 4 ∨ n = 5 ∨ n = 7) := by
  interval_cases n
  · exact iff_of_false (not_brocard_of_bounds 0 1 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 1 1 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 2 1 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 3 2 (by decide) (by decide)) (by decide)
  · exact iff_of_true ⟨5, by decide⟩ (by decide)
  · exact iff_of_true ⟨11, by decide⟩ (by decide)
  · exact iff_of_false (not_brocard_of_bounds 6 26 (by decide) (by decide)) (by decide)
  · exact iff_of_true ⟨71, by decide⟩ (by decide)
  · exact iff_of_false (not_brocard_of_bounds 8 200 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 9 602 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 10 1904 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 11 6317 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 12 21886 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 13 78911 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 14 295259 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 15 1143535 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 16 4574143 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 17 18859677 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 18 80014834 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 19 348776576 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 20 1559776268 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 21 7147792818 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 22 33526120082 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 23 160785623545 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 24 787685471322 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 25 3938427356614 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 26 20082117944245 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 27 104349745809073 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 28 552166953567228 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 29 2973510046012910 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 30 16286585271694955 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 31 90679869067935485 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 32 512962802680363491 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 33 2946746955341073478 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 34 17182339742875652406 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 35 101652092779175702171 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 36 609912556675054213027 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 37 3709953246501409085690 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 38 22869687743093501007951 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 39 142821154179615294686593 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 40 903280290523322408635610 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 41 5783815921445270815783609 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 42 37483411234209726053065805 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 43 245795164849461258960674062 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 44 1630420674178430788228519563 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 45 10937194378152021970306618007 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 46 74179661362209580727623742159 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 47 508550136674023695658451670185 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 48 3523338699662022653505900576721 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 49 24663370897634158574541304037050 (by decide) (by decide)) (by decide)
  · exact iff_of_false (not_brocard_of_bounds 50 174396368086360611696209329639024 (by decide) (by decide)) (by decide)

/-- **Brocard Gap Conjecture (conditional reduction).**

Assume the pronic form of Brocard's problem beyond the verified range: for every `n ≥ 8` the
factorial `n !` is never of the form `4 * u * (u + 1)`.  (By `isBrocard_iff_pronic` this
hypothesis says exactly that no `n ≥ 8` is a Brocard number; it is the only unproven input, and
it is verified unconditionally for `8 ≤ n ≤ 50` in `isBrocard_iff_of_le_50`.)

Then:
* the Brocard numbers are precisely `4`, `5`, `7`; and
* the *gap* statement holds: apart from the initial pair `(4,5)`, no two consecutive integers are
  both Brocard numbers. -/
theorem BrocardGapConjecture
    (hred : ∀ n : ℕ, 8 ≤ n → ∀ u : ℕ, n ! ≠ 4 * u * (u + 1)) :
    (∀ n : ℕ, IsBrocard n ↔ (n = 4 ∨ n = 5 ∨ n = 7)) ∧
      (∀ n : ℕ, 5 ≤ n → ¬ (IsBrocard n ∧ IsBrocard (n + 1))) := by
  have key : ∀ n : ℕ, IsBrocard n ↔ (n = 4 ∨ n = 5 ∨ n = 7) := by
    intro n
    by_cases hn : n ≤ 50
    · exact isBrocard_iff_of_le_50 n hn
    · push_neg at hn
      refine iff_of_false ?_ (by omega)
      intro hb
      obtain ⟨u, hu⟩ := (isBrocard_iff_pronic n (by omega)).1 hb
      exact hred n (by omega) u hu
  refine ⟨key, ?_⟩
  rintro n hn ⟨h1, h2⟩
  have hA := (key n).1 h1
  have hB := (key (n + 1)).1 h2
  omega

end Brockian.BrocardGap

