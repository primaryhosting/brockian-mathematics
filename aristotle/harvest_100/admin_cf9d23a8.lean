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
This module is deliberately self-contained: it uses no imports beyond Lean's core
`Init`, so that the header comment above can be the very first thing in the file.
Everything below (the Collatz map, its iteration, and all lemmas) is developed
from scratch.

The Collatz conjecture itself is open. What is proved here is:

* `collatzConjecture_iff_mod_four` — the conjecture reduces to the residue class 3 mod 4;
* `collatzConjecture_iff_hardResidue` — it reduces further to the three residue classes
  7, 11, 15 modulo 16;
* `collatzConjecture_iff_eventual_descent` — the conjecture is equivalent to the statement
  that every `n > 1` is eventually mapped below itself;
* `exists_minimal_counterexample` — contrapositive form: a failure of the conjecture yields
  a least counterexample, which must lie in one of those three classes mod 16;
* `cycle_trivial_of_reaches1` and `cycle_trivial_of_lt_1000` — every Collatz cycle meeting
  `{n : 0 < n < 1000}` is the trivial cycle `1 → 4 → 2 → 1`;
* `reaches1_of_lt_1000` — an exhaustive kernel-checked verification for all `0 < n < 1000`;
* `reaches1_two_pow` — every power of two reaches 1.
-/

namespace Brockian.CollatzPartial

/-! ## The Collatz map -/

/-- One step of the Collatz (`3n + 1`) map: halve an even number, otherwise `n ↦ 3n + 1`. -/
def step (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `iter k n` is the result of applying the Collatz map `k` times to `n`. -/
def iter : Nat → Nat → Nat
  | 0, n => n
  | (k + 1), n => iter k (step n)

/-- `Reaches1 n` says that some iterate of the Collatz map sends `n` to `1`. -/
def Reaches1 (n : Nat) : Prop := ∃ k : Nat, iter k n = 1

/-- **The Collatz conjecture**: every positive natural number eventually reaches `1`
under iteration of the Collatz map `n ↦ n/2` (`n` even), `n ↦ 3n+1` (`n` odd).

This is the honest, unconditional statement of the open problem, packaged as a `Prop`.
The theorems in this file are Lean-checked *partial* results about it and *conditional
reductions* of it (see the file header). -/
def CollatzConjecture : Prop := ∀ n : Nat, 0 < n → Reaches1 n

/-! ## Basic lemmas about iteration -/

theorem iter_zero (n : Nat) : iter 0 n = n := rfl

theorem iter_succ (k n : Nat) : iter (k + 1) n = iter k (step n) := rfl

theorem iter_succ' (k n : Nat) : iter (k + 1) n = step (iter k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => rw [iter_succ (k + 1) n, ih (step n), iter_succ k n]

theorem iter_add (a b n : Nat) : iter (a + b) n = iter a (iter b n) := by
  induction b generalizing n with
  | zero => rfl
  | succ b ih =>
    show iter (a + b + 1) n = iter a (iter (b + 1) n)
    rw [iter_succ (a + b) n, iter_succ b n, ih (step n)]

/-! ## Basic properties of the step map -/

theorem step_of_even {n : Nat} (h : n % 2 = 0) : step n = n / 2 := by
  simp [step, h]

theorem step_of_odd {n : Nat} (h : n % 2 = 1) : step n = 3 * n + 1 := by
  simp [step, h]

theorem step_pos {n : Nat} (h : 0 < n) : 0 < step n := by
  unfold step
  split <;> omega

theorem iter_pos {n : Nat} (h : 0 < n) (k : Nat) : 0 < iter k n := by
  induction k generalizing n with
  | zero => exact h
  | succ k ih => rw [iter_succ]; exact ih (step_pos h)

/-! ## Elementary facts about `Reaches1` -/

theorem reaches1_one : Reaches1 1 := ⟨0, rfl⟩

theorem reaches1_of_iter {n k : Nat} (h : Reaches1 (iter k n)) : Reaches1 n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j + k, by rw [iter_add]; exact hj⟩

theorem reaches1_of_step {n : Nat} (h : Reaches1 (step n)) : Reaches1 n :=
  reaches1_of_iter (k := 1) h

theorem step_one : step 1 = 4 := by decide

theorem step_two : step 2 = 1 := by decide

theorem step_four : step 4 = 2 := by decide

theorem reaches1_two : Reaches1 2 := reaches1_of_step (by rw [step_two]; exact reaches1_one)

theorem reaches1_four : Reaches1 4 := reaches1_of_step (by rw [step_four]; exact reaches1_two)

/-- Every power of two reaches `1`. -/
theorem reaches1_two_pow (k : Nat) : Reaches1 (2 ^ k) := by
  induction k with
  | zero => exact reaches1_one
  | succ k ih =>
    refine reaches1_of_step ?_
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ]; omega
    have he : 2 ^ (k + 1) % 2 = 0 := by omega
    rw [step_of_even he]
    have : 2 ^ (k + 1) / 2 = 2 ^ k := by omega
    rw [this]
    exact ih

/-! ## Descent away from the residue class `3 mod 4` -/

/-- Three Collatz steps applied to `4 * m + 1` give `3 * m + 1`. -/
theorem iter_three_of_mod_four_one (m : Nat) : iter 3 (4 * m + 1) = 3 * m + 1 := by
  have h : iter 3 (4 * m + 1) = step (step (step (4 * m + 1))) := rfl
  have e1 : step (4 * m + 1) = 12 * m + 4 := by
    rw [step_of_odd (by omega)]; omega
  have e2 : step (12 * m + 4) = 6 * m + 2 := by
    rw [step_of_even (by omega)]; omega
  have e3 : step (6 * m + 2) = 3 * m + 1 := by
    rw [step_of_even (by omega)]; omega
  rw [h, e1, e2, e3]

/-- Six Collatz steps applied to `16 * k + 3` give `9 * k + 2`. -/
theorem iter_six_of_mod_sixteen_three (k : Nat) : iter 6 (16 * k + 3) = 9 * k + 2 := by
  have h : iter 6 (16 * k + 3)
      = step (step (step (step (step (step (16 * k + 3)))))) := rfl
  have e1 : step (16 * k + 3) = 48 * k + 10 := by
    rw [step_of_odd (by omega)]; omega
  have e2 : step (48 * k + 10) = 24 * k + 5 := by
    rw [step_of_even (by omega)]; omega
  have e3 : step (24 * k + 5) = 72 * k + 16 := by
    rw [step_of_odd (by omega)]; omega
  have e4 : step (72 * k + 16) = 36 * k + 8 := by
    rw [step_of_even (by omega)]; omega
  have e5 : step (36 * k + 8) = 18 * k + 4 := by
    rw [step_of_even (by omega)]; omega
  have e6 : step (18 * k + 4) = 9 * k + 2 := by
    rw [step_of_even (by omega)]; omega
  rw [h, e1, e2, e3, e4, e5, e6]

/-- If `n > 1` and `n` is not congruent to `3` modulo `4`, then a positive number of Collatz
steps strictly decreases `n`. -/
theorem exists_iter_lt_of_mod_four_ne_three {n : Nat} (h1 : 1 < n) (h4 : n % 4 ≠ 3) :
    ∃ k : Nat, 0 < k ∧ iter k n < n := by
  rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with he | ho
  · refine ⟨1, by omega, ?_⟩
    rw [iter_succ, iter_zero, step_of_even he]
    omega
  · have h41 : n % 4 = 1 := by omega
    obtain ⟨m, hm⟩ : ∃ m, n = 4 * m + 1 := ⟨n / 4, by omega⟩
    refine ⟨3, by omega, ?_⟩
    rw [hm, iter_three_of_mod_four_one]
    omega

/-- The "hard" residues modulo `16`, i.e. those for which the argument below provides no
uniform descent. -/
def HardResidue (n : Nat) : Prop := n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15

/-- **Descent lemma.** If `n > 1` is not in one of the three hard residue classes modulo `16`,
then a positive number of Collatz steps strictly decreases `n`. -/
theorem exists_iter_lt_of_not_hard {n : Nat} (h1 : 1 < n) (h : ¬ HardResidue n) :
    ∃ k : Nat, 0 < k ∧ iter k n < n := by
  have h7 : n % 16 ≠ 7 := fun hh => h (Or.inl hh)
  have h11 : n % 16 ≠ 11 := fun hh => h (Or.inr (Or.inl hh))
  have h15 : n % 16 ≠ 15 := fun hh => h (Or.inr (Or.inr hh))
  rcases (by omega : n % 4 ≠ 3 ∨ n % 16 = 3) with h4 | h16
  · exact exists_iter_lt_of_mod_four_ne_three h1 h4
  · obtain ⟨k, hk⟩ : ∃ k, n = 16 * k + 3 := ⟨n / 16, by omega⟩
    refine ⟨6, by omega, ?_⟩
    rw [hk, iter_six_of_mod_sixteen_three]
    omega

/-! ## Minimal counterexample (contrapositive form) -/

/-- **Contrapositive / minimal-counterexample form.** If the Collatz conjecture fails, then
there is a *least* counterexample, and it necessarily lies in one of the three hard residue
classes `7, 11, 15` modulo `16` (in particular it satisfies `n ≡ 3 [MOD 4]`). -/
theorem exists_minimal_counterexample (h : ¬ CollatzConjecture) :
    ∃ n : Nat, 1 < n ∧ HardResidue n ∧ ¬ Reaches1 n ∧
      ∀ m : Nat, 0 < m → m < n → Reaches1 m := by
  refine Classical.byContradiction fun hno => h ?_
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    refine Classical.byContradiction fun hnR => ?_
    -- by strong induction every smaller positive number reaches 1
    have hmin : ∀ m : Nat, 0 < m → m < n → Reaches1 m := fun m hm hmn => ih m hmn hm
    have h1 : 1 < n := by
      rcases (by omega : n = 1 ∨ 1 < n) with rfl | h1
      · exact absurd reaches1_one hnR
      · exact h1
    have h4 : HardResidue n := by
      refine Classical.byContradiction fun h4 => ?_
      obtain ⟨k, _, hlt⟩ := exists_iter_lt_of_not_hard h1 h4
      exact hnR (reaches1_of_iter (hmin _ (iter_pos hn k) hlt))
    exact hno ⟨n, h1, h4, hnR, hmin⟩

/-- A hard residue is congruent to `3` modulo `4`. -/
theorem mod_four_eq_three_of_hardResidue {n : Nat} (h : HardResidue n) : n % 4 = 3 := by
  rcases h with h | h | h <;> omega

/-- **Reduction to one residue class.** The Collatz conjecture is equivalent to its restriction
to the numbers congruent to `3` modulo `4`. -/
theorem collatzConjecture_iff_mod_four :
    CollatzConjecture ↔ ∀ n : Nat, 0 < n → n % 4 = 3 → Reaches1 n := by
  constructor
  · intro h n hn _
    exact h n hn
  · intro h
    refine Classical.byContradiction fun hc => ?_
    obtain ⟨n, h1, h4, hnR, _⟩ := exists_minimal_counterexample hc
    exact hnR (h n (by omega) (mod_four_eq_three_of_hardResidue h4))

/-- **Reduction to three residue classes modulo 16.** The Collatz conjecture is equivalent to
its restriction to the numbers congruent to `7`, `11` or `15` modulo `16`. -/
theorem collatzConjecture_iff_hardResidue :
    CollatzConjecture ↔ ∀ n : Nat, 0 < n → HardResidue n → Reaches1 n := by
  constructor
  · intro h n hn _
    exact h n hn
  · intro h
    refine Classical.byContradiction fun hc => ?_
    obtain ⟨n, h1, h4, hnR, _⟩ := exists_minimal_counterexample hc
    exact hnR (h n (by omega) h4)

/-! ## Reduction to eventual descent -/

/-- **Equivalent reformulation.** The Collatz conjecture holds if and only if every `n > 1`
is mapped strictly below itself after finitely many (at least one) Collatz steps. -/
theorem collatzConjecture_iff_eventual_descent :
    CollatzConjecture ↔ ∀ n : Nat, 1 < n → ∃ k : Nat, 0 < k ∧ iter k n < n := by
  constructor
  · intro h n h1
    obtain ⟨k, hk⟩ := h n (by omega)
    refine ⟨k, ?_, ?_⟩
    · rcases (by omega : k = 0 ∨ 0 < k) with rfl | hk0
      · rw [iter_zero] at hk; omega
      · exact hk0
    · rw [hk]; omega
  · intro h
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro hn
      rcases (by omega : n = 1 ∨ 1 < n) with rfl | h1
      · exact reaches1_one
      · obtain ⟨k, _, hlt⟩ := h n h1
        exact reaches1_of_iter (ih _ hlt (iter_pos hn k))

/-! ## Cycles -/

/-- The orbit of `1` is the three-element cycle `1 → 4 → 2 → 1`. -/
theorem iter_one_mem (k : Nat) : iter k 1 = 1 ∨ iter k 1 = 2 ∨ iter k 1 = 4 := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rw [iter_succ']
    rcases ih with h | h | h
    · rw [h, step_one]; exact Or.inr (Or.inr rfl)
    · rw [h, step_two]; exact Or.inl rfl
    · rw [h, step_four]; exact Or.inr (Or.inl rfl)

theorem iter_mul (p t n : Nat) (h : iter p n = n) : iter (p * t) n = n := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hmul : p * (t + 1) = p + p * t := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [hmul, iter_add, ih, h]

/-- A periodic point that reaches `1` lies on the trivial cycle. -/
theorem cycle_trivial_of_reaches1 {m p : Nat} (hp : 0 < p) (hper : iter p m = m)
    (hR : Reaches1 m) : m = 1 ∨ m = 2 ∨ m = 4 := by
  obtain ⟨K, hK⟩ := hR
  have hle : K ≤ p * K := Nat.le_mul_of_pos_left K hp
  have h1 : iter (p * K) m = m := iter_mul p K m hper
  have h2 : iter (p * K - K + K) m = iter (p * K - K) (iter K m) := iter_add _ _ _
  rw [Nat.sub_add_cancel hle, h1, hK] at h2
  rw [h2]
  exact iter_one_mem _

/-! ## Exhaustive verification for small values -/

/-- Fuelled Boolean test: does `n` reach `1` within `fuel` Collatz steps? -/
def reachesWithin : Nat → Nat → Bool
  | 0, n => n == 1
  | (f + 1), n => n == 1 || reachesWithin f (step n)

theorem reaches1_of_reachesWithin : ∀ (f n : Nat), reachesWithin f n = true → Reaches1 n := by
  intro f
  induction f with
  | zero =>
    intro n h
    simp only [reachesWithin, beq_iff_eq] at h
    exact h ▸ reaches1_one
  | succ f ih =>
    intro n h
    simp only [reachesWithin, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact h ▸ reaches1_one
    · exact reaches1_of_step (ih _ h)

set_option maxRecDepth 10000 in
private theorem reachesWithin_lt_1000 : ∀ n < 1000, 0 < n → reachesWithin 200 n = true := by
  decide

/-- **Verified partial result.** Every `n` with `0 < n < 1000` reaches `1`. -/
theorem reaches1_of_lt_1000 {n : Nat} (hn : 0 < n) (h : n < 1000) : Reaches1 n :=
  reaches1_of_reachesWithin 200 n (reachesWithin_lt_1000 n h hn)

/-- **No small nontrivial cycles.** Any Collatz cycle containing a positive number below
`1000` is the trivial cycle `1 → 4 → 2 → 1`. -/
theorem cycle_trivial_of_lt_1000 {m p : Nat} (hm : 0 < m) (hlt : m < 1000) (hp : 0 < p)
    (hper : iter p m = m) : m = 1 ∨ m = 2 ∨ m = 4 :=
  cycle_trivial_of_reaches1 hp hper (reaches1_of_lt_1000 hm hlt)

end Brockian.CollatzPartial

