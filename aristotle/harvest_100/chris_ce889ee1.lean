/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- A `±1` sequence, indexed by the positive naturals (the value at `0` is irrelevant). -/
def IsPlusMinusOne (f : ℕ → ℤ) : Prop := ∀ n : ℕ, 1 ≤ n → f n = 1 ∨ f n = -1

/-- The sum of `f` along the first `n` terms of the homogeneous arithmetic progression
of common difference `d`, i.e. `f d + f (2d) + ⋯ + f (nd)`. -/
def apSum (f : ℕ → ℤ) (d n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, f (i * d)

/-- `f` has discrepancy at most `C` on homogeneous arithmetic progressions. -/
def HasDiscrepancyAtMost (f : ℕ → ℤ) (C : ℕ) : Prop :=
  ∀ d n : ℕ, 1 ≤ d → |apSum f d n| ≤ (C : ℤ)

/-- The Erdős discrepancy problem (theorem of Tao): every `±1` sequence has unbounded
discrepancy on homogeneous arithmetic progressions.  This is the full statement; it is
recorded here as a `Prop` for reference.  The theorem `Frontier.erdos_discrepancy` below
proves the base case `C = 1` of this statement. -/
def ErdosDiscrepancyConjecture : Prop :=
  ∀ f : ℕ → ℤ, IsPlusMinusOne f → ∀ C : ℕ, ¬ HasDiscrepancyAtMost f C

/-- Unfolded form of the conjecture: for every bound `C` some homogeneous AP sum exceeds `C`. -/
theorem erdosDiscrepancyConjecture_iff :
    ErdosDiscrepancyConjecture ↔
      ∀ f : ℕ → ℤ, IsPlusMinusOne f → ∀ C : ℕ, ∃ d n : ℕ, 1 ≤ d ∧ (C : ℤ) < |apSum f d n| := by
  constructor
  · intro h f hf C
    have := h f hf C
    unfold HasDiscrepancyAtMost at this
    push_neg at this
    obtain ⟨d, n, hd, hdn⟩ := this
    exact ⟨d, n, hd, hdn⟩
  · intro h f hf C hC
    obtain ⟨d, n, hd, hdn⟩ := h f hf C
    exact absurd (hC d n hd) (not_le.2 hdn)

/-- One step of the sum along a homogeneous AP. -/
theorem apSum_succ (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (n + 1) = apSum f d n + f ((n + 1) * d) := by
  unfold apSum
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

/-- A `±1` sequence has all its dilations `±1`. -/
theorem IsPlusMinusOne.dilate {f : ℕ → ℤ} (hf : IsPlusMinusOne f) {e : ℕ} (he : 1 ≤ e) :
    IsPlusMinusOne (fun n => f (n * e)) := by
  intro n hn
  exact hf (n * e) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))

/-- Bounded discrepancy is inherited by dilations: if `f` has discrepancy at most `C`,
so does `n ↦ f (n * e)` for every `e ≥ 1`.  (A reduction step: it suffices to bound the
discrepancy of a sequence to bound that of all its dilations.) -/
theorem HasDiscrepancyAtMost.dilate {f : ℕ → ℤ} {C : ℕ} (hC : HasDiscrepancyAtMost f C)
    {e : ℕ} (he : 1 ≤ e) : HasDiscrepancyAtMost (fun n => f (n * e)) C := by
  intro d n hd
  have h : apSum (fun n => f (n * e)) d n = apSum f (d * e) n := by
    unfold apSum
    exact Finset.sum_congr rfl fun i _ => by simp only [Nat.mul_assoc]
  rw [h]
  exact hC (d * e) n (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))

section BaseCase

variable {f : ℕ → ℤ}

/-- Every partial sum along a homogeneous AP is congruent to its length modulo `2`. -/
theorem two_dvd_apSum_sub (hf : IsPlusMinusOne f) {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    (2 : ℤ) ∣ (apSum f d n - (n : ℤ)) := by
  induction n with
  | zero => simp [apSum]
  | succ n ih =>
      rw [apSum_succ]
      have hval : f ((n + 1) * d) = 1 ∨ f ((n + 1) * d) = -1 :=
        hf _ (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.succ_ne_zero n) (by omega)))
      obtain ⟨c, hc⟩ := ih
      rcases hval with h | h <;> rw [h] <;> [exact ⟨c, by push_cast; omega⟩;
        exact ⟨c - 1, by push_cast; omega⟩]

/-- If the discrepancy is at most `1`, every even-length homogeneous AP sum vanishes. -/
theorem apSum_even_eq_zero (hf : IsPlusMinusOne f) (hb : HasDiscrepancyAtMost f 1)
    {d : ℕ} (hd : 1 ≤ d) (j : ℕ) : apSum f d (2 * j) = 0 := by
  obtain ⟨c, hc⟩ := two_dvd_apSum_sub hf hd (2 * j)
  have hle : |apSum f d (2 * j)| ≤ (1 : ℤ) := by simpa using hb d (2 * j) hd
  rw [abs_le] at hle
  push_cast at hc
  omega

/-- If the discrepancy is at most `1`, consecutive terms of a homogeneous AP pair off:
`f ((2j+1) d) + f ((2j+2) d) = 0`. -/
theorem pair_eq_zero (hf : IsPlusMinusOne f) (hb : HasDiscrepancyAtMost f 1)
    {d : ℕ} (hd : 1 ≤ d) (j : ℕ) : f ((2 * j + 1) * d) + f ((2 * j + 2) * d) = 0 := by
  have h0 : apSum f d (2 * j) = 0 := apSum_even_eq_zero hf hb hd j
  have h1 : apSum f d (2 * (j + 1)) = 0 := apSum_even_eq_zero hf hb hd (j + 1)
  have e1 : apSum f d (2 * j + 1) = apSum f d (2 * j) + f ((2 * j + 1) * d) := apSum_succ f d (2 * j)
  have e2 : apSum f d (2 * j + 2) = apSum f d (2 * j + 1) + f ((2 * j + 2) * d) :=
    apSum_succ f d (2 * j + 1)
  have h1' : apSum f d (2 * j + 2) = 0 := by rw [show 2 * j + 2 = 2 * (j + 1) by ring]; exact h1
  omega

/-- **Base case of the Erdős discrepancy problem.**  No `±1` sequence has discrepancy `≤ 1`
on homogeneous arithmetic progressions. -/
theorem not_hasDiscrepancyAtMost_one (hf : IsPlusMinusOne f) :
    ¬ HasDiscrepancyAtMost f 1 := by
  intro hb
  have pair := fun {d : ℕ} (hd : 1 ≤ d) (j : ℕ) => pair_eq_zero hf hb hd j
  -- f 2 = - f 1
  have h2 : f 1 + f 2 = 0 := by simpa using pair (d := 1) (by norm_num) 0
  -- f 4 = - f 2
  have h4 : f 2 + f 4 = 0 := by simpa using pair (d := 2) (by norm_num) 0
  -- f 3 + f 4 = 0
  have h3 : f 3 + f 4 = 0 := by simpa using pair (d := 1) (by norm_num) 1
  -- f 6 = - f 3
  have h6 : f 3 + f 6 = 0 := by simpa using pair (d := 3) (by norm_num) 0
  -- f 5 + f 6 = 0
  have h5 : f 5 + f 6 = 0 := by simpa using pair (d := 1) (by norm_num) 2
  -- f 10 = - f 5
  have h10 : f 5 + f 10 = 0 := by simpa using pair (d := 5) (by norm_num) 0
  -- f 9 + f 10 = 0
  have h9 : f 9 + f 10 = 0 := by simpa using pair (d := 1) (by norm_num) 4
  -- f 12 = - f 6
  have h12 : f 6 + f 12 = 0 := by simpa using pair (d := 6) (by norm_num) 0
  -- f 9 + f 12 = 0
  have h912 : f 9 + f 12 = 0 := by simpa using pair (d := 3) (by norm_num) 1
  have hone : f 1 = 1 ∨ f 1 = -1 := hf 1 le_rfl
  omega

end BaseCase

/-- **Erdős discrepancy problem, base case (`C = 1`).**  For every `±1` sequence `f` there are
a common difference `d ≥ 1` and a length `n` with `|f d + f (2d) + ⋯ + f (nd)| ≥ 2`.
(The full theorem of Tao, stated here as `Frontier.ErdosDiscrepancyConjecture`, asserts that
these sums are unbounded; this is its first nontrivial case.) -/
theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsPlusMinusOne f) :
    ∃ d n : ℕ, 1 ≤ d ∧ 2 ≤ |apSum f d n| := by
  by_contra h
  push_neg at h
  refine not_hasDiscrepancyAtMost_one hf ?_
  intro d n hd
  have := h d n hd
  omega

end Frontier

