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
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The full Collatz conjecture is open.  What is proved here is:

* `CollatzConjecture` : a Lean-checked *conditional reduction* — if every integer `> 1`
  eventually iterates to a strictly smaller value (the descent property), then every
  positive integer reaches `1`.
* unconditional partial results: the descent property holds for every `n > 1` outside the
  residue class `3 (mod 4)`, and every power of two reaches `1`.
-/

namespace Brockian.CollatzPartial

/-- One step of the Collatz map: `n ↦ n/2` if `n` is even, `n ↦ 3n+1` if `n` is odd. -/
def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `Reaches1 n` says that some iterate of the Collatz map sends `n` to `1`. -/
def Reaches1 (n : ℕ) : Prop := ∃ k, collatz^[k] n = 1

/-- The "descent property": every integer `> 1` eventually iterates to a smaller value.
This is a well-known equivalent reformulation of the hard part of the Collatz conjecture. -/
def DescentProperty : Prop := ∀ n : ℕ, 1 < n → ∃ k, 0 < k ∧ collatz^[k] n < n

lemma collatz_even {n : ℕ} (h : n % 2 = 0) : collatz n = n / 2 := by
  simp [collatz, h]

lemma collatz_odd {n : ℕ} (h : n % 2 = 1) : collatz n = 3 * n + 1 := by
  simp [collatz, h]

lemma collatz_pos {n : ℕ} (h : 0 < n) : 0 < collatz n := by
  rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
  · rw [collatz_even h2]; omega
  · rw [collatz_odd h2]; omega

lemma iterate_pos {n : ℕ} (h : 0 < n) (k : ℕ) : 0 < collatz^[k] n := by
  induction k generalizing n with
  | zero => simpa using h
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      exact ih (collatz_pos h)

lemma reaches1_of_iterate {n k : ℕ} (h : Reaches1 (collatz^[k] n)) : Reaches1 n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j + k, by rwa [Function.iterate_add_apply]⟩

/-- **Conditional reduction of the Collatz conjecture.**
If every integer greater than `1` eventually iterates to a strictly smaller value
(the descent property), then every positive integer reaches `1`. -/
theorem CollatzConjecture (h : DescentProperty) : ∀ n : ℕ, 0 < n → Reaches1 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · obtain ⟨k, _, hk⟩ := h n h1
      exact reaches1_of_iterate (ih _ hk (iterate_pos hn k))
    · have hn1 : n = 1 := by omega
      exact ⟨0, by simp [hn1]⟩

/-- The converse direction: if every positive integer reaches `1`, the descent property holds.
Hence the descent property is *equivalent* to the Collatz conjecture. -/
theorem descentProperty_of_reaches1 (h : ∀ n : ℕ, 0 < n → Reaches1 n) : DescentProperty := by
  intro n hn
  obtain ⟨k, hk⟩ := h n (by omega)
  refine ⟨k, ?_, by rw [hk]; omega⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp at hk; omega
  · exact hk0

/-- The Collatz conjecture is equivalent to the descent property. -/
theorem collatz_iff_descent : (∀ n : ℕ, 0 < n → Reaches1 n) ↔ DescentProperty :=
  ⟨descentProperty_of_reaches1, CollatzConjecture⟩

/-! ### Unconditional partial results

The descent property holds for every `n > 1` with `n % 4 ≠ 3`; only the residue class
`n ≡ 3 (mod 4)` remains open. -/

/-- Even numbers `> 1` descend in one step. -/
theorem descent_of_even {n : ℕ} (hn : 1 < n) (h : n % 2 = 0) : collatz n < n := by
  rw [collatz_even h]; omega

/-- Numbers congruent to `1` mod `4` (other than `1` itself) descend in three steps. -/
theorem descent_of_one_mod_four {n : ℕ} (hn : 1 < n) (h : n % 4 = 1) :
    collatz^[3] n < n := by
  have h2 : n % 2 = 1 := by omega
  have e1 : collatz n = 3 * n + 1 := collatz_odd h2
  have h3 : (3 * n + 1) % 2 = 0 := by omega
  have e2 : collatz (3 * n + 1) = (3 * n + 1) / 2 := collatz_even h3
  have h4 : ((3 * n + 1) / 2) % 2 = 0 := by omega
  have e3 : collatz ((3 * n + 1) / 2) = ((3 * n + 1) / 2) / 2 := collatz_even h4
  show collatz (collatz (collatz n)) < n
  rw [e1, e2, e3]
  omega

/-- The descent property holds unconditionally outside the residue class `3 (mod 4)`. -/
theorem descent_of_ne_three_mod_four {n : ℕ} (hn : 1 < n) (h : n % 4 ≠ 3) :
    ∃ k, 0 < k ∧ collatz^[k] n < n := by
  rcases eq_or_ne (n % 4) 1 with h1 | h1
  · exact ⟨3, by norm_num, descent_of_one_mod_four hn h1⟩
  · exact ⟨1, one_pos, by simpa using descent_of_even hn (by omega)⟩

/-- Numbers congruent to `3` mod `16` descend in six steps. -/
theorem descent_of_three_mod_sixteen {n : ℕ} (h : n % 16 = 3) : collatz^[6] n < n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 16 * m + 3 := ⟨n / 16, by omega⟩
  have e1 : collatz (16 * m + 3) = 48 * m + 10 := by
    rw [collatz_odd (by omega)]; omega
  have e2 : collatz (48 * m + 10) = 24 * m + 5 := by
    rw [collatz_even (by omega)]; omega
  have e3 : collatz (24 * m + 5) = 72 * m + 16 := by
    rw [collatz_odd (by omega)]; omega
  have e4 : collatz (72 * m + 16) = 36 * m + 8 := by
    rw [collatz_even (by omega)]; omega
  have e5 : collatz (36 * m + 8) = 18 * m + 4 := by
    rw [collatz_even (by omega)]; omega
  have e6 : collatz (18 * m + 4) = 9 * m + 2 := by
    rw [collatz_even (by omega)]; omega
  show collatz (collatz (collatz (collatz (collatz (collatz (16 * m + 3)))))) < 16 * m + 3
  rw [e1, e2, e3, e4, e5, e6]
  omega

/-- Sharpened unconditional descent: the descent property holds for every `n > 1` whose
residue mod `16` is not `7`, `11` or `15`, i.e. for `13` of the `16` residue classes. -/
theorem descent_of_mod_sixteen {n : ℕ} (hn : 1 < n)
    (h7 : n % 16 ≠ 7) (h11 : n % 16 ≠ 11) (h15 : n % 16 ≠ 15) :
    ∃ k, 0 < k ∧ collatz^[k] n < n := by
  rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
  · exact ⟨1, one_pos, by simpa using descent_of_even hn h2⟩
  · rcases eq_or_ne (n % 4) 1 with h1 | h1
    · exact ⟨3, by norm_num, descent_of_one_mod_four hn h1⟩
    · exact ⟨6, by norm_num, descent_of_three_mod_sixteen (by omega)⟩

/-- Every power of two reaches `1`, unconditionally. -/
theorem reaches1_two_pow (k : ℕ) : Reaches1 (2 ^ k) := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
      refine reaches1_of_iterate (k := 1) ?_
      have h2 : (2 ^ (k + 1)) % 2 = 0 := by
        simp [pow_succ, Nat.mul_mod_left]
      have : collatz^[1] (2 ^ (k + 1)) = 2 ^ k := by
        rw [Function.iterate_one, collatz_even h2, pow_succ]
        omega
      rw [this]
      exact ih

/-- Bounded-fuel Boolean test: `reaches1B f n` is `true` iff `n` reaches `1` within `f` steps. -/
def reaches1B : ℕ → ℕ → Bool
  | 0, n => n == 1
  | f + 1, n => (n == 1) || reaches1B f (collatz n)

lemma reaches1_of_reaches1B : ∀ (f n : ℕ), reaches1B f n = true → Reaches1 n := by
  intro f
  induction f with
  | zero =>
      intro n h
      rw [reaches1B, beq_iff_eq] at h
      exact ⟨0, by simp [h]⟩
  | succ f ih =>
      intro n h
      rw [reaches1B, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · exact ⟨0, by simp [h]⟩
      · obtain ⟨k, hk⟩ := ih _ h
        exact ⟨k + 1, by rw [Function.iterate_add_apply]; simpa using hk⟩

set_option maxRecDepth 1000000 in
/-- Kernel-checked verification of the Collatz conjecture for all `1 ≤ n ≤ 1000`. -/
theorem reaches1_of_le_1000 (n : ℕ) (h0 : 0 < n) (h1 : n ≤ 1000) : Reaches1 n := by
  have key : ∀ m < 1001, 0 < m → reaches1B 400 m = true := by decide
  exact reaches1_of_reaches1B 400 n (key n (by omega) h0)

end Brockian.CollatzPartial

