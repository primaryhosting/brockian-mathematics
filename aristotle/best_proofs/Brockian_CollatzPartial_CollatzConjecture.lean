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
-- (Lean 4 requires `import` to precede any module docstring, so the header above is a
-- plain comment and is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CollatzPartial

/-- One step of the Collatz map: `n ↦ n / 2` if `n` is even, `n ↦ 3 * n + 1` if `n` is odd. -/
def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `ReachesOne n` says that some iterate of the Collatz map sends `n` to `1`. -/
def ReachesOne (n : ℕ) : Prop := ∃ k : ℕ, collatz^[k] n = 1

/-- Orbits of positive numbers stay positive. -/
lemma collatz_pos {n : ℕ} (hn : 0 < n) : 0 < collatz n := by
  unfold collatz
  split <;> omega

lemma collatz_iterate_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < collatz^[k] n := by
  induction k with
  | zero => simpa using hn
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact collatz_pos ih

@[simp] lemma collatz_one : collatz 1 = 4 := by decide
@[simp] lemma collatz_two : collatz 2 = 1 := by decide
@[simp] lemma collatz_four : collatz 4 = 2 := by decide

lemma reachesOne_one : ReachesOne 1 := ⟨0, rfl⟩

lemma reachesOne_two : ReachesOne 2 := ⟨1, by simp⟩

lemma reachesOne_four : ReachesOne 4 := ⟨2, by
  simp [Function.iterate_succ_apply]⟩

/-- Doubling: if `n` reaches `1`, so does `2 * n` (for `n` positive). -/
lemma reachesOne_two_mul {n : ℕ} (h : ReachesOne n) : ReachesOne (2 * n) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k + 1, ?_⟩
  have : collatz (2 * n) = n := by
    unfold collatz
    have h2 : (2 * n) % 2 = 0 := by omega
    simp [h2]
  rw [Function.iterate_succ_apply, this, hk]

/-- Unconditional partial result: every power of two reaches `1`. -/
theorem reachesOne_two_pow (k : ℕ) : ReachesOne (2 ^ k) := by
  induction k with
  | zero => simpa using reachesOne_one
  | succ k ih =>
      have : (2:ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [this]
      exact reachesOne_two_mul ih

/-- A fuel-based decision procedure: `reachesOneCheck f n = true` witnesses that `n`
reaches `1` within `f` steps. -/
def reachesOneCheck : ℕ → ℕ → Bool
  | 0, n => n == 1
  | f + 1, n => n == 1 || reachesOneCheck f (collatz n)

lemma reachesOne_of_check : ∀ (f n : ℕ), reachesOneCheck f n = true → ReachesOne n := by
  intro f
  induction f with
  | zero =>
      intro n h
      simp [reachesOneCheck] at h
      exact ⟨0, by simp [h]⟩
  | succ f ih =>
      intro n h
      rw [reachesOneCheck] at h
      rcases Bool.or_eq_true_iff.mp h with h1 | h1
      · exact ⟨0, by simpa using (beq_iff_eq.mp h1)⟩
      · obtain ⟨k, hk⟩ := ih _ h1
        exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

/-- Unconditional partial result: every `n` with `1 ≤ n ≤ 40` reaches `1`. -/
theorem reachesOne_of_le_forty (n : ℕ) (hn : 0 < n) (hle : n ≤ 40) : ReachesOne n := by
  refine reachesOne_of_check 130 n ?_
  interval_cases n <;> rfl

/-- If a positive number has a bounded orbit, then some point of its orbit is periodic. -/
lemma exists_periodic_of_bounded {n : ℕ} {B : ℕ}
    (hB : ∀ k : ℕ, collatz^[k] n ≤ B) :
    ∃ (i t : ℕ), 0 < t ∧ collatz^[t] (collatz^[i] n) = collatz^[i] n := by
  -- the orbit lands in a finite set, so the iteration map is not injective
  set f : ℕ → Fin (B + 1) := fun k => ⟨collatz^[k] n, Nat.lt_succ_of_le (hB k)⟩
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : ∀ a b : ℕ, a < b → collatz^[a] n = collatz^[b] n →
      ∃ (i t : ℕ), 0 < t ∧ collatz^[t] (collatz^[i] n) = collatz^[i] n := by
    intro a b hlt heq
    refine ⟨a, b - a, by omega, ?_⟩
    rw [← Function.iterate_add_apply]
    have : b - a + a = b := by omega
    rw [this, ← heq]
  have heq : collatz^[a] n = collatz^[b] n := congrArg Fin.val hfab
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h heq
  · exact key b a h heq.symm

/--
**Collatz Conjecture (conditional reduction).**

Assuming
* `hbdd`: every positive integer has a bounded Collatz orbit (no divergent trajectory), and
* `hcyc`: the only periodic points of the Collatz map among the positive integers are
  `1`, `2`, `4` (no nontrivial cycle),

every positive integer eventually reaches `1`.

Both hypotheses are necessary conditions for the Collatz conjecture (see
`bounded_of_collatz` and `cycle_of_collatz` below), so this is an exact reduction of
the conjecture to the conjunction "no divergent orbit" ∧ "no nontrivial cycle".
-/
theorem CollatzConjecture
    (hbdd : ∀ n : ℕ, 0 < n → ∃ B : ℕ, ∀ k : ℕ, collatz^[k] n ≤ B)
    (hcyc : ∀ m : ℕ, 0 < m → ∀ t : ℕ, 0 < t → collatz^[t] m = m →
      m = 1 ∨ m = 2 ∨ m = 4) :
    ∀ n : ℕ, 0 < n → ReachesOne n := by
  intro n hn
  obtain ⟨B, hB⟩ := hbdd n hn
  obtain ⟨i, t, ht, hper⟩ := exists_periodic_of_bounded hB
  set m := collatz^[i] n with hm
  have hmpos : 0 < m := collatz_iterate_pos hn i
  have hmem := hcyc m hmpos t ht hper
  have hmreach : ReachesOne m := by
    rcases hmem with h | h | h
    · rw [h]; exact reachesOne_one
    · rw [h]; exact reachesOne_two
    · rw [h]; exact reachesOne_four
  obtain ⟨k, hk⟩ := hmreach
  exact ⟨k + i, by rw [Function.iterate_add_apply, ← hm, hk]⟩

/-- Conversely, the Collatz conjecture implies that every positive orbit is bounded. -/
theorem bounded_of_collatz (h : ∀ n : ℕ, 0 < n → ReachesOne n) :
    ∀ n : ℕ, 0 < n → ∃ B : ℕ, ∀ k : ℕ, collatz^[k] n ≤ B := by
  intro n hn
  obtain ⟨k, hk⟩ := h n hn
  -- after step `k` the orbit cycles through `1, 4, 2`, so it is bounded by
  -- the max of the finitely many first values and `4`
  refine ⟨max 4 ((Finset.range (k + 1)).sup fun j => collatz^[j] n), ?_⟩
  intro j
  by_cases hjk : j ≤ k
  · refine le_trans ?_ (le_max_right _ _)
    exact Finset.le_sup (f := fun j => collatz^[j] n) (Finset.mem_range.mpr (by omega))
  · replace hjk : k < j := by omega
    -- `j = k + r` with `r > 0`; the tail is the cycle `1 → 4 → 2 → 1`
    have hcyc : ∀ r : ℕ, collatz^[r] 1 ≤ 4 := by
      intro r
      induction r using Nat.strong_induction_on with
      | _ r ih =>
        match r with
        | 0 => simp
        | 1 => simp
        | 2 => simp [Function.iterate_succ_apply]
        | (m + 3) =>
          have h3 : collatz^[3] 1 = 1 := by
            simp [Function.iterate_succ_apply]
          have : collatz^[m + 3] 1 = collatz^[m] (collatz^[3] 1) := by
            rw [← Function.iterate_add_apply]
          rw [this, h3]
          exact ih m (by omega)
    have hsplit : collatz^[j] n = collatz^[j - k] (collatz^[k] n) := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rw [hsplit, hk]
    exact le_trans (hcyc (j - k)) (le_max_left _ _)

/-- Conversely, the Collatz conjecture implies the only positive periodic points are `1, 2, 4`. -/
theorem cycle_of_collatz (h : ∀ n : ℕ, 0 < n → ReachesOne n) :
    ∀ m : ℕ, 0 < m → ∀ t : ℕ, 0 < t → collatz^[t] m = m → m = 1 ∨ m = 2 ∨ m = 4 := by
  intro m hm t ht hper
  obtain ⟨k, hk⟩ := h m hm
  -- `m` is periodic, hence it lies on the cycle through `1`
  have hiter : ∀ s : ℕ, collatz^[s * t] m = m := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
        have : (s + 1) * t = t + s * t := by ring
        rw [this, Function.iterate_add_apply, ih, hper]
  -- choose a multiple of `t` at least `k`, so that `m` equals an iterate of `1`
  have hmk : collatz^[k * t] m = m := hiter k
  have h1 : collatz^[k * t - k] (collatz^[k] m) = m := by
    rw [← Function.iterate_add_apply]
    have : k * t - k + k = k * t := by
      have : k ≤ k * t := Nat.le_mul_of_pos_right k ht
      omega
    rw [this, hmk]
  rw [hk] at h1
  -- iterates of `1` are `1, 4, 2` cyclically
  have hcyc : ∀ r : ℕ, collatz^[r] 1 = 1 ∨ collatz^[r] 1 = 4 ∨ collatz^[r] 1 = 2 := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      match r with
      | 0 => simp
      | 1 => simp
      | 2 => simp [Function.iterate_succ_apply]
      | (p + 3) =>
        have h3 : collatz^[3] 1 = 1 := by simp [Function.iterate_succ_apply]
        have : collatz^[p + 3] 1 = collatz^[p] (collatz^[3] 1) := by
          rw [← Function.iterate_add_apply]
        rw [this, h3]
        exact ih p (by omega)
  rcases hcyc (k * t - k) with hh | hh | hh <;> rw [hh] at h1
  · exact Or.inl h1.symm
  · exact Or.inr (Or.inr h1.symm)
  · exact Or.inr (Or.inl h1.symm)

end Brockian.CollatzPartial

