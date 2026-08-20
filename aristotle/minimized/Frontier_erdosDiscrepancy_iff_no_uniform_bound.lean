import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

/-- A `±1` sequence, indexed by the positive integers. -/

def IsPlusMinusOne (f : ℕ → ℤ) : Prop := ∀ n, 1 ≤ n → f n = 1 ∨ f n = -1

/-- The discrepancy sum of `f` along the homogeneous arithmetic progression of common
difference `d`, truncated after `n` terms: `f d + f 2d + ⋯ + f nd`. -/

def apSum (f : ℕ → ℤ) (d n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, f (i * d)

/-- **The Erdős discrepancy problem** (a theorem of Tao, 2015), as a formal statement:
every `±1` sequence has unbounded discrepancy along homogeneous arithmetic progressions,
i.e. for every bound `C` there are `d, n ≥ 1` with `|f d + f 2d + ⋯ + f nd| > C`. -/

def ErdosDiscrepancy : Prop :=
  ∀ f : ℕ → ℤ, IsPlusMinusOne f → ∀ C : ℤ, ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ C < |apSum f d n|

/-- Reduction: the Erdős discrepancy statement is equivalent to saying that no `±1`
sequence admits a uniform bound on its discrepancy over homogeneous APs. -/

theorem erdosDiscrepancy_iff_no_uniform_bound :
    ErdosDiscrepancy ↔
      ∀ f : ℕ → ℤ, IsPlusMinusOne f →
        ¬ ∃ C : ℤ, ∀ d n : ℕ, 0 < d → 0 < n → |apSum f d n| ≤ C := by
  constructor
  · rintro h f hf ⟨C, hC⟩
    obtain ⟨d, n, hd, hn, hlt⟩ := h f hf C
    exact absurd (hC d n hd hn) (not_le.2 hlt)
  · intro h f hf C
    by_contra hcon
    push_neg at hcon
    exact h f hf ⟨C, fun d n hd hn => hcon d n hd hn⟩

/-- Key finite step: a `±1` sequence whose discrepancy over homogeneous APs never exceeds
`1` does not exist.  Only the progressions with `d * n ≤ 12`, hence only the values
`f 1, …, f 12`, are involved. -/
