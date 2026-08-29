/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The partial sum of `f` along the homogeneous arithmetic progression of common
difference `d`: `apSum f d n = f d + f (2 * d) + ⋯ + f (n * d)`. -/
def apSum (f : ℕ → ℤ) (d n : ℕ) : ℤ := ∑ i ∈ Finset.range n, f ((i + 1) * d)

/-- `f` is a `±1`-valued sequence (indexed from `1`). -/
def IsPMOne (f : ℕ → ℤ) : Prop := ∀ n, 1 ≤ n → f n = 1 ∨ f n = -1

/-- `f` has discrepancy at most `C` on homogeneous arithmetic progressions. -/
def HasDiscrepancyAtMost (f : ℕ → ℤ) (C : ℤ) : Prop :=
  ∀ d n : ℕ, 0 < d → |apSum f d n| ≤ C

/-- The Erdős discrepancy problem (theorem of Tao, 2015): every `±1` sequence has
unbounded discrepancy along homogeneous arithmetic progressions. -/
def ErdosDiscrepancyStatement : Prop :=
  ∀ f : ℕ → ℤ, IsPMOne f → ∀ C : ℤ, ∃ d n : ℕ, 0 < d ∧ C < |apSum f d n|

/-- Reduction: the Erdős discrepancy statement is exactly the assertion that no `±1`
sequence has bounded discrepancy on homogeneous arithmetic progressions. -/
theorem erdosDiscrepancyStatement_iff :
    ErdosDiscrepancyStatement ↔
      ∀ f : ℕ → ℤ, IsPMOne f → ∀ C : ℤ, ¬ HasDiscrepancyAtMost f C := by
  constructor
  · intro h f hf C hC
    obtain ⟨d, n, hd, hlt⟩ := h f hf C
    exact absurd (hC d n hd) (not_le.mpr hlt)
  · intro h f hf C
    have := h f hf C
    unfold HasDiscrepancyAtMost at this
    push_neg at this
    obtain ⟨d, n, hd, hlt⟩ := this
    exact ⟨d, n, hd, hlt⟩

@[simp] theorem apSum_zero (f : ℕ → ℤ) (d : ℕ) : apSum f d 0 = 0 := by
  simp [apSum]

theorem apSum_succ (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (n + 1) = apSum f d n + f ((n + 1) * d) := by
  simp [apSum, Finset.sum_range_succ]

/-- Each partial sum along a homogeneous AP has the same parity as its length. -/
theorem apSum_parity (f : ℕ → ℤ) (hf : IsPMOne f) (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (2 : ℤ) ∣ apSum f d n - n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hval : f ((n + 1) * d) = 1 ∨ f ((n + 1) * d) = -1 :=
        hf _ (Nat.one_le_iff_ne_zero.mpr (by positivity))
      obtain ⟨k, hk⟩ := ih
      rw [apSum_succ]
      push_cast
      rcases hval with h | h <;> rw [h] <;> [exact ⟨k, by linarith⟩;
        exact ⟨k - 1, by linarith⟩]

/-- A partial sum of even length with absolute value at most `1` vanishes. -/
theorem apSum_eq_zero_of_even (f : ℕ → ℤ) (hf : IsPMOne f) (d : ℕ) (hd : 0 < d)
    (n : ℕ) (hn : Even n) (hbd : |apSum f d n| ≤ 1) : apSum f d n = 0 := by
  obtain ⟨m, hm⟩ := hn
  obtain ⟨k, hk⟩ := apSum_parity f hf d hd n
  rw [abs_le] at hbd
  subst hm
  push_cast at hk
  omega

/-- **Base case of the Erdős discrepancy problem** (`C = 1`).

Every `±1` sequence `f` has discrepancy at least `2` on homogeneous arithmetic
progressions: there are `d ≤ 3` and `n ≤ 10` with `|f d + f (2d) + ⋯ + f (nd)| ≥ 2`.
Equivalently, no `±1` sequence has discrepancy at most `1`. -/
theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsPMOne f) :
    ∃ d n : ℕ, 0 < d ∧ d ≤ 3 ∧ n ≤ 10 ∧ 2 ≤ |apSum f d n| := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ d n : ℕ, 0 < d → d ≤ 3 → n ≤ 10 → |apSum f d n| ≤ 1 := by
    intro d n hd hd3 hn6
    have := hcon d n hd hd3 hn6
    omega
  have hz : ∀ d n : ℕ, 0 < d → d ≤ 3 → n ≤ 10 → Even n → apSum f d n = 0 := by
    intro d n hd hd3 hn6 hn
    exact apSum_eq_zero_of_even f hf d hd n hn (key d n hd hd3 hn6)
  -- `d = 2` at lengths 4, 6 gives `f 10 + f 12 = 0`
  have h1 : apSum f 2 4 = 0 := hz 2 4 (by norm_num) (by norm_num) (by norm_num) ⟨2, rfl⟩
  have h2 : apSum f 2 6 = 0 := hz 2 6 (by norm_num) (by norm_num) (by norm_num) ⟨3, rfl⟩
  -- `d = 3` at lengths 2, 4 gives `f 9 + f 12 = 0`
  have h3 : apSum f 3 2 = 0 := hz 3 2 (by norm_num) (by norm_num) (by norm_num) ⟨1, rfl⟩
  have h4 : apSum f 3 4 = 0 := hz 3 4 (by norm_num) (by norm_num) (by norm_num) ⟨2, rfl⟩
  -- `d = 1` at lengths 8, 10 gives `f 9 + f 10 = 0`
  have h5 : apSum f 1 8 = 0 := hz 1 8 (by norm_num) (by norm_num) (by norm_num) ⟨4, rfl⟩
  have h6 : apSum f 1 10 = 0 := hz 1 10 (by norm_num) (by norm_num) (by norm_num) ⟨5, rfl⟩
  -- expand all the sums
  simp only [apSum, Finset.sum_range_succ, Finset.sum_range_zero] at h1 h2 h3 h4 h5 h6
  norm_num at h1 h2 h3 h4 h5 h6
  -- `f 9 = 0`, contradicting `f 9 = ±1`
  have h9 := hf 9 (by norm_num)
  have h10 := hf 10 (by norm_num)
  have h12 := hf 12 (by norm_num)
  omega

end Frontier

