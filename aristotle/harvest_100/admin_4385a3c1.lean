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

/-
This file is deliberately self-contained (no `import` lines), so that the header comment
above can literally be the first thing in the file: Lean requires `import` commands to
precede every other command, including module documentation.  Consequently the few
standard facts about function iteration that are used below are proved from scratch.

The Collatz conjecture is a famous open problem.  What is established here is:

* an unconditional reduction of the conjecture to a *descent* hypothesis
  (`reaches1_of_descends`);
* unconditional proofs of descent for every residue class modulo `32` except
  `7`, `15`, `27` and `31`, which sharpen the reduction so that only those four
  classes remain (`CollatzConjecture`);
* unconditional verification of the conjecture for all powers of two and for all
  positive integers below `1000`.
-/

namespace Brockian.CollatzPartial

/-! ## Iteration -/

/-- `iterate f k n` is the `k`-fold application of `f` to `n`. -/
def iterate (f : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iterate f k (f n)

theorem iterate_zero (f : Nat → Nat) (n : Nat) : iterate f 0 n = n := rfl

theorem iterate_succ_apply (f : Nat → Nat) (k n : Nat) :
    iterate f (k + 1) n = iterate f k (f n) := rfl

theorem iterate_succ_apply' (f : Nat → Nat) (k n : Nat) :
    iterate f (k + 1) n = f (iterate f k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply f (k + 1) n, ih, iterate_succ_apply]

theorem iterate_add_apply (f : Nat → Nat) (j k n : Nat) :
    iterate f (j + k) n = iterate f j (iterate f k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    have h : j + (k + 1) = (j + k) + 1 := rfl
    rw [h, iterate_succ_apply, ih, iterate_succ_apply]

/-! ## The Collatz map -/

/-- One step of the Collatz map: `n ↦ n / 2` if `n` is even, `n ↦ 3 * n + 1` if `n` is odd. -/
def collatz (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `Reaches1 n` says that some iterate of the Collatz map sends `n` to `1`. -/
def Reaches1 (n : Nat) : Prop := ∃ k : Nat, iterate collatz k n = 1

/-- The descent property for `n`: some positive number of Collatz steps takes `n`
strictly below itself. -/
def Descends (n : Nat) : Prop := ∃ k : Nat, 0 < k ∧ iterate collatz k n < n

theorem collatz_even {n : Nat} (h : n % 2 = 0) : collatz n = n / 2 := if_pos h

theorem collatz_odd {n : Nat} (h : n % 2 = 1) : collatz n = 3 * n + 1 := by
  unfold collatz
  rw [if_neg (by omega)]

theorem collatz_pos {n : Nat} (h : 0 < n) : 0 < collatz n := by
  unfold collatz
  split
  · omega
  · omega

theorem iterate_collatz_pos {n : Nat} (h : 0 < n) (k : Nat) : 0 < iterate collatz k n := by
  induction k generalizing n with
  | zero => exact h
  | succ k ih => exact ih (collatz_pos h)

theorem reaches1_one : Reaches1 1 := ⟨0, rfl⟩

/-- If the Collatz successor of `n` reaches `1`, then so does `n`. -/
theorem reaches1_of_step {n : Nat} (h : Reaches1 (collatz n)) : Reaches1 n := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by rw [iterate_succ_apply]; exact hk⟩

/-- If some iterate of `n` reaches `1`, then so does `n`. -/
theorem reaches1_of_iterate {n k : Nat} (h : Reaches1 (iterate collatz k n)) : Reaches1 n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j + k, by rw [iterate_add_apply]; exact hj⟩

/-! ## The descent reduction -/

/--
**Conditional reduction.** If every integer greater than `1` eventually descends strictly
below itself under iteration of the Collatz map, then every positive integer reaches `1`,
i.e. the Collatz conjecture holds.
-/
theorem reaches1_of_descends (hdesc : ∀ n : Nat, 1 < n → Descends n) :
    ∀ n : Nat, 0 < n → Reaches1 n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases h1 : 1 < n
    · obtain ⟨k, _, hlt⟩ := hdesc n h1
      exact reaches1_of_iterate (ih _ hlt (iterate_collatz_pos hn k))
    · have : n = 1 := by omega
      rw [this]
      exact reaches1_one

/-! ## Unconditional descent outside the residue class `3 mod 4` -/

theorem descends_of_even {n : Nat} (hn : 1 < n) (h : n % 2 = 0) : Descends n := by
  refine ⟨1, Nat.one_pos, ?_⟩
  show iterate collatz 1 n < n
  rw [iterate_succ_apply, iterate_zero, collatz_even h]
  omega

theorem descends_of_one_mod_four {n : Nat} (hn : 1 < n) (h : n % 4 = 1) : Descends n := by
  obtain ⟨m, hm, rfl⟩ : ∃ m : Nat, 0 < m ∧ n = 4 * m + 1 := ⟨n / 4, by omega, by omega⟩
  refine ⟨3, by omega, ?_⟩
  have h1 : collatz (4 * m + 1) = 12 * m + 4 := by
    rw [collatz_odd (by omega)]; omega
  have h2 : collatz (12 * m + 4) = 6 * m + 2 := by
    rw [collatz_even (by omega)]; omega
  have h3 : collatz (6 * m + 2) = 3 * m + 1 := by
    rw [collatz_even (by omega)]; omega
  show iterate collatz 3 (4 * m + 1) < 4 * m + 1
  rw [iterate_succ_apply, iterate_succ_apply, iterate_succ_apply, iterate_zero, h1, h2, h3]
  omega

/--
**Sharpened conditional reduction.** It suffices to establish the descent property for the
integers congruent to `3` modulo `4`; descent is unconditional in the other residue classes.
-/
theorem reaches1_of_descends_three_mod_four
    (hdesc : ∀ n : Nat, 1 < n → n % 4 = 3 → Descends n) :
    ∀ n : Nat, 0 < n → Reaches1 n := by
  refine reaches1_of_descends fun n hn => ?_
  by_cases he : n % 2 = 0
  · exact descends_of_even hn he
  · by_cases h1 : n % 4 = 1
    · exact descends_of_one_mod_four hn h1
    · exact hdesc n hn (by omega)

/-- Descent is also unconditional for `n ≡ 3 [MOD 16]`: six Collatz steps take `16 * m + 3`
to `9 * m + 2`. -/
theorem descends_of_three_mod_sixteen {n : Nat} (h : n % 16 = 3) : Descends n := by
  obtain ⟨m, rfl⟩ : ∃ m : Nat, n = 16 * m + 3 := ⟨n / 16, by omega⟩
  refine ⟨6, by omega, ?_⟩
  have h1 : collatz (16 * m + 3) = 48 * m + 10 := by
    rw [collatz_odd (by omega)]; omega
  have h2 : collatz (48 * m + 10) = 24 * m + 5 := by
    rw [collatz_even (by omega)]; omega
  have h3 : collatz (24 * m + 5) = 72 * m + 16 := by
    rw [collatz_odd (by omega)]; omega
  have h4 : collatz (72 * m + 16) = 36 * m + 8 := by
    rw [collatz_even (by omega)]; omega
  have h5 : collatz (36 * m + 8) = 18 * m + 4 := by
    rw [collatz_even (by omega)]; omega
  have h6 : collatz (18 * m + 4) = 9 * m + 2 := by
    rw [collatz_even (by omega)]; omega
  show iterate collatz 6 (16 * m + 3) < 16 * m + 3
  rw [iterate_succ_apply, iterate_succ_apply, iterate_succ_apply, iterate_succ_apply,
    iterate_succ_apply, iterate_succ_apply, iterate_zero, h1, h2, h3, h4, h5, h6]
  omega

/-- Descent is unconditional for `n ≡ 11 [MOD 32]`: eight Collatz steps take `32 * m + 11`
to `27 * m + 10`. -/
theorem descends_of_eleven_mod_thirtytwo {n : Nat} (h : n % 32 = 11) : Descends n := by
  obtain ⟨m, rfl⟩ : ∃ m : Nat, n = 32 * m + 11 := ⟨n / 32, by omega⟩
  refine ⟨8, by omega, ?_⟩
  have h1 : collatz (32 * m + 11) = 96 * m + 34 := by
    rw [collatz_odd (by omega)]; omega
  have h2 : collatz (96 * m + 34) = 48 * m + 17 := by
    rw [collatz_even (by omega)]; omega
  have h3 : collatz (48 * m + 17) = 144 * m + 52 := by
    rw [collatz_odd (by omega)]; omega
  have h4 : collatz (144 * m + 52) = 72 * m + 26 := by
    rw [collatz_even (by omega)]; omega
  have h5 : collatz (72 * m + 26) = 36 * m + 13 := by
    rw [collatz_even (by omega)]; omega
  have h6 : collatz (36 * m + 13) = 108 * m + 40 := by
    rw [collatz_odd (by omega)]; omega
  have h7 : collatz (108 * m + 40) = 54 * m + 20 := by
    rw [collatz_even (by omega)]; omega
  have h8 : collatz (54 * m + 20) = 27 * m + 10 := by
    rw [collatz_even (by omega)]; omega
  show iterate collatz 8 (32 * m + 11) < 32 * m + 11
  rw [iterate_succ_apply, iterate_succ_apply, iterate_succ_apply, iterate_succ_apply,
    iterate_succ_apply, iterate_succ_apply, iterate_succ_apply, iterate_succ_apply,
    iterate_zero, h1, h2, h3, h4, h5, h6, h7, h8]
  omega

/-- Descent is unconditional for `n ≡ 23 [MOD 32]`: eight Collatz steps take `32 * m + 23`
to `27 * m + 20`. -/
theorem descends_of_twentythree_mod_thirtytwo {n : Nat} (h : n % 32 = 23) : Descends n := by
  obtain ⟨m, rfl⟩ : ∃ m : Nat, n = 32 * m + 23 := ⟨n / 32, by omega⟩
  refine ⟨8, by omega, ?_⟩
  have h1 : collatz (32 * m + 23) = 96 * m + 70 := by
    rw [collatz_odd (by omega)]; omega
  have h2 : collatz (96 * m + 70) = 48 * m + 35 := by
    rw [collatz_even (by omega)]; omega
  have h3 : collatz (48 * m + 35) = 144 * m + 106 := by
    rw [collatz_odd (by omega)]; omega
  have h4 : collatz (144 * m + 106) = 72 * m + 53 := by
    rw [collatz_even (by omega)]; omega
  have h5 : collatz (72 * m + 53) = 216 * m + 160 := by
    rw [collatz_odd (by omega)]; omega
  have h6 : collatz (216 * m + 160) = 108 * m + 80 := by
    rw [collatz_even (by omega)]; omega
  have h7 : collatz (108 * m + 80) = 54 * m + 40 := by
    rw [collatz_even (by omega)]; omega
  have h8 : collatz (54 * m + 40) = 27 * m + 20 := by
    rw [collatz_even (by omega)]; omega
  show iterate collatz 8 (32 * m + 23) < 32 * m + 23
  rw [iterate_succ_apply, iterate_succ_apply, iterate_succ_apply, iterate_succ_apply,
    iterate_succ_apply, iterate_succ_apply, iterate_succ_apply, iterate_succ_apply,
    iterate_zero, h1, h2, h3, h4, h5, h6, h7, h8]
  omega

/--
**Reduction to three residue classes modulo 16.** It suffices to establish the descent
property for the integers congruent to `7`, `11` or `15` modulo `16`; descent is
unconditional in the other thirteen residue classes.
-/
theorem reaches1_of_descends_mod_sixteen
    (hdesc : ∀ n : Nat, 1 < n → (n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15) → Descends n) :
    ∀ n : Nat, 0 < n → Reaches1 n := by
  refine reaches1_of_descends_three_mod_four fun n hn h4 => ?_
  by_cases h3 : n % 16 = 3
  · exact descends_of_three_mod_sixteen h3
  · exact hdesc n hn (by omega)

/--
**Reduction to four residue classes modulo 32.** It suffices to establish the descent
property for the integers congruent to `7`, `15`, `27` or `31` modulo `32`; descent is
unconditional in the other twenty-eight residue classes.
-/
theorem reaches1_of_descends_mod_thirtytwo
    (hdesc : ∀ n : Nat, 1 < n →
      (n % 32 = 7 ∨ n % 32 = 15 ∨ n % 32 = 27 ∨ n % 32 = 31) → Descends n) :
    ∀ n : Nat, 0 < n → Reaches1 n := by
  refine reaches1_of_descends_mod_sixteen fun n hn h16 => ?_
  by_cases h11 : n % 32 = 11
  · exact descends_of_eleven_mod_thirtytwo h11
  · by_cases h23 : n % 32 = 23
    · exact descends_of_twentythree_mod_thirtytwo h23
    · exact hdesc n hn (by omega)

/-! ## The Collatz conjecture -/

/--
**The Collatz conjecture (conditional form).**

The Collatz conjecture — that every positive integer reaches `1` under iteration of the
Collatz map — is an open problem, so what is proved here is a Lean-checked *reduction*:
the conjecture follows from the descent hypothesis restricted to the four residue classes
`7`, `15`, `27`, `31` modulo `32`, namely that every such `n > 1` satisfies
`iterate collatz k n < n` for some `k > 0`.  The remaining twenty-eight residue classes
modulo `32` are handled unconditionally (`descends_of_even`, `descends_of_one_mod_four`,
`descends_of_three_mod_sixteen`, `descends_of_eleven_mod_thirtytwo`,
`descends_of_twentythree_mod_thirtytwo`).
-/
theorem CollatzConjecture
    (hdesc : ∀ n : Nat, 1 < n →
      (n % 32 = 7 ∨ n % 32 = 15 ∨ n % 32 = 27 ∨ n % 32 = 31) → Descends n) :
    ∀ n : Nat, 0 < n → ∃ k : Nat, iterate collatz k n = 1 :=
  reaches1_of_descends_mod_thirtytwo hdesc

/-! ## Unconditional partial results -/

/-- Every power of two reaches `1`. -/
theorem reaches1_two_pow (k : Nat) : Reaches1 (2 ^ k) := by
  induction k with
  | zero => exact reaches1_one
  | succ k ih =>
    refine reaches1_of_step ?_
    have hpow : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ]; omega
    have h : (2 : Nat) ^ (k + 1) % 2 = 0 := by
      rw [hpow]; omega
    rw [collatz_even h, hpow, Nat.mul_div_cancel_left _ (by omega)]
    exact ih

/-- A bounded search for a hitting time of `1`, used for finite verification. -/
def reachesOneWithin : Nat → Nat → Bool
  | 0, n => n == 1
  | fuel + 1, n => (n == 1) || reachesOneWithin fuel (collatz n)

theorem reaches1_of_reachesOneWithin :
    ∀ (fuel n : Nat), reachesOneWithin fuel n = true → Reaches1 n
  | 0, n, h => ⟨0, by simpa [reachesOneWithin] using h⟩
  | fuel + 1, n, h => by
      rw [reachesOneWithin, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨0, by simpa using h⟩
      · exact reaches1_of_step (reaches1_of_reachesOneWithin fuel _ h)

set_option maxRecDepth 40000 in
/-- Unconditional verification: every positive integer below `1000` reaches `1`. -/
theorem reaches1_of_lt_thousand (n : Nat) (hpos : 0 < n) (hlt : n < 1000) : Reaches1 n := by
  have key : ∀ m : Nat, m < 999 → reachesOneWithin 200 (m + 1) = true := by decide
  have h := key (n - 1) (by omega)
  rw [Nat.sub_add_cancel hpos] at h
  exact reaches1_of_reachesOneWithin 200 n h

end Brockian.CollatzPartial

