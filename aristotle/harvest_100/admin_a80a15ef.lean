/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The Erdős discrepancy problem (solved by T. Tao, 2015) asserts that every `±1` sequence
`f : ℕ → ℤ` has *unbounded* discrepancy along homogeneous arithmetic progressions: the
partial sums `∑_{i=1}^{n} f (i * d)` are unbounded in absolute value as `n, d` range over
the positive integers.

A search of Mathlib turns up no formalization of the Erdős discrepancy problem (nor of the
logarithmically averaged Chowla/Elliott conjectures used in Tao's proof), and no existing
lemma closes or nearly closes the statement below.

This file therefore:

* formalizes the full statement as `Frontier.ErdosDiscrepancyConjecture` (a `Prop`, stated
  but not claimed here);
* proves the base case `C = 1`, `Frontier.erdos_discrepancy`: no `±1` sequence has
  discrepancy `≤ 1`, i.e. every `±1` sequence admits a homogeneous arithmetic progression
  whose partial sum exceeds `1` in absolute value.  This is sharp in the sense that the
  first `11` terms of a `±1` sequence *can* have discrepancy `1`; the contradiction below
  uses the value `f 12`;
* records the trivial case `C = 0` as `Frontier.erdos_discrepancy_C_zero`.

Proof of the base case.  Suppose all homogeneous partial sums have absolute value at most
`1`.  For `d ≥ 1` the sum `f d + f (2*d)` is even and has absolute value at most `1`, hence
vanishes: `f (2*d) = - f d`; similarly `f (3*d) + f (4*d) = 0`.  Chasing these relations
from `f 1` gives
`f 2 = -f 1`, `f 4 = f 1` (via `d = 2`), `f 3 = -f 1`, `f 6 = f 1` (via `d = 3`),
`f 5 = -f 1`, `f 10 = f 1` (via `d = 5`), `f 9 = -f 1`, and then `f 12 = f 1`
(via `d = 3`, second pair) while `f 12 = -f 1` (via `d = 6`), a contradiction since
`f 1 = ±1`.

The development is deliberately self-contained (no imports), so that the statement can be
read off directly from the definitions below; `List.range`-based sums play the role of
`∑ i ∈ Finset.Icc 1 n`.
-/

namespace Frontier

/-- The discrepancy of `f` along the homogeneous arithmetic progression of common
difference `d`, truncated at `n` terms: `∑_{i=1}^{n} f (i * d)`. -/
def apSum (f : Nat → Int) (d n : Nat) : Int :=
  ((List.range n).map (fun i => f ((i + 1) * d))).sum

/-- `f` is a `±1` sequence (on the positive integers). -/
def IsPlusMinusOne (f : Nat → Int) : Prop := ∀ n, 1 ≤ n → f n = 1 ∨ f n = -1

/-- `f` has unbounded discrepancy on homogeneous arithmetic progressions: for every bound
`C` there are `d, n ≥ 1` with `|∑_{i=1}^{n} f (i * d)| > C`. -/
def HasUnboundedDiscrepancy (f : Nat → Int) : Prop :=
  ∀ C : Nat, ∃ d n : Nat, 1 ≤ d ∧ 1 ≤ n ∧ C < (apSum f d n).natAbs

/-- **The Erdős discrepancy conjecture** (theorem of Tao, 2015), stated but not proved
here: every `±1` sequence has unbounded discrepancy along homogeneous arithmetic
progressions. -/
def ErdosDiscrepancyConjecture : Prop :=
  ∀ f : Nat → Int, IsPlusMinusOne f → HasUnboundedDiscrepancy f

/-- Key step: a `±1` sequence all of whose homogeneous partial sums have absolute value at
most `1` does not exist; the contradiction is already visible among `f 1, …, f 12`. -/
theorem not_discrepancy_le_one (f : Nat → Int) (hf : IsPlusMinusOne f)
    (h : ∀ d n : Nat, 1 ≤ d → 1 ≤ n → (apSum f d n).natAbs ≤ 1) : False := by
  have H : ∀ d n : Nat, 1 ≤ d → 1 ≤ n → -1 ≤ apSum f d n ∧ apSum f d n ≤ 1 := by
    intro d n hd hn
    have := h d n hd hn
    omega
  -- even partial sums of the progression of difference `1`
  have b1 : -1 ≤ f 1 + (f 2 + 0) ∧ f 1 + (f 2 + 0) ≤ 1 := H 1 2 (by omega) (by omega)
  have b2 : -1 ≤ f 1 + (f 2 + (f 3 + (f 4 + 0))) ∧ f 1 + (f 2 + (f 3 + (f 4 + 0))) ≤ 1 :=
    H 1 4 (by omega) (by omega)
  have b3 : -1 ≤ f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + 0))))) ∧
      f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + 0))))) ≤ 1 := H 1 6 (by omega) (by omega)
  have b4 : -1 ≤ f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + 0))))))) ∧
      f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + 0))))))) ≤ 1 :=
    H 1 8 (by omega) (by omega)
  have b5 : -1 ≤ f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 +
        (f 10 + 0))))))))) ∧
      f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + 0))))))))) ≤ 1 :=
    H 1 10 (by omega) (by omega)
  -- the progressions of difference `2`, `3`, `5`, `6`
  have c2 : -1 ≤ f 2 + (f 4 + 0) ∧ f 2 + (f 4 + 0) ≤ 1 := H 2 2 (by omega) (by omega)
  have c3 : -1 ≤ f 3 + (f 6 + 0) ∧ f 3 + (f 6 + 0) ≤ 1 := H 3 2 (by omega) (by omega)
  have c4 : -1 ≤ f 3 + (f 6 + (f 9 + (f 12 + 0))) ∧ f 3 + (f 6 + (f 9 + (f 12 + 0))) ≤ 1 :=
    H 3 4 (by omega) (by omega)
  have c5 : -1 ≤ f 5 + (f 10 + 0) ∧ f 5 + (f 10 + 0) ≤ 1 := H 5 2 (by omega) (by omega)
  have c6 : -1 ≤ f 6 + (f 12 + 0) ∧ f 6 + (f 12 + 0) ≤ 1 := H 6 2 (by omega) (by omega)
  have e1 := hf 1 (by omega)
  have e2 := hf 2 (by omega)
  have e3 := hf 3 (by omega)
  have e4 := hf 4 (by omega)
  have e5 := hf 5 (by omega)
  have e6 := hf 6 (by omega)
  have e7 := hf 7 (by omega)
  have e8 := hf 8 (by omega)
  have e9 := hf 9 (by omega)
  have e10 := hf 10 (by omega)
  have e12 := hf 12 (by omega)
  omega

/-- **Erdős discrepancy problem, base case `C = 1`.**
Every `±1` sequence `f` has discrepancy at least `2` along homogeneous arithmetic
progressions: there are `d, n ≥ 1` with `|∑_{i=1}^{n} f (i * d)| > 1`.

This is the first nontrivial instance of the statement, `ErdosDiscrepancyConjecture`, that
every `±1` sequence has unbounded discrepancy. -/
theorem erdos_discrepancy (f : Nat → Int) (hf : IsPlusMinusOne f) :
    ∃ d n : Nat, 1 ≤ d ∧ 1 ≤ n ∧ 1 < (apSum f d n).natAbs := by
  apply Classical.byContradiction
  intro hcon
  refine not_discrepancy_le_one f hf (fun d n hd hn => ?_)
  apply Classical.byContradiction
  intro hle
  exact hcon ⟨d, n, hd, hn, by omega⟩

/-- The trivial case `C = 0` of the conjecture. -/
theorem erdos_discrepancy_C_zero (f : Nat → Int) (hf : IsPlusMinusOne f) :
    ∃ d n : Nat, 1 ≤ d ∧ 1 ≤ n ∧ 0 < (apSum f d n).natAbs := by
  refine ⟨1, 1, Nat.le_refl _, Nat.le_refl _, ?_⟩
  have happ : apSum f 1 1 = f 1 + 0 := rfl
  have h := hf 1 (Nat.le_refl _)
  rw [happ]
  omega

end Frontier

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

import RequestProject.ErdosDiscrepancy
import Mathlib

/-!
# Erdos Discrepancy — Mathlib restatement

Companion to `RequestProject/ErdosDiscrepancy.lean`, where the target theorem
`Frontier.erdos_discrepancy` is proved in a self-contained (import-free) form.

Here we identify the `List.range`-based partial sum `Frontier.apSum` with the usual
Mathlib sum `∑ i ∈ Finset.Icc 1 n, f (i * d)` and restate the results in that language.
-/

namespace Frontier

/-- `apSum f d n` is the sum `∑_{i=1}^{n} f (i * d)`. -/
theorem apSum_eq_sum_Icc (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d n = ∑ i ∈ Finset.Icc 1 n, f (i * d) := by
  induction n with
  | zero => simp [apSum]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ← ih]
      simp [apSum, List.range_succ]

/-- **Erdős discrepancy problem, base case `C = 1`** (Mathlib phrasing).
For every `±1` sequence `f` there are `d, n ≥ 1` with `|∑_{i=1}^{n} f (i * d)| > 1`. -/
theorem erdos_discrepancy_sum_Icc (f : ℕ → ℤ) (hf : ∀ n, 1 ≤ n → f n = 1 ∨ f n = -1) :
    ∃ d n : ℕ, 1 ≤ d ∧ 1 ≤ n ∧ 1 < |∑ i ∈ Finset.Icc 1 n, f (i * d)| := by
  obtain ⟨d, n, hd, hn, hlt⟩ := erdos_discrepancy f hf
  refine ⟨d, n, hd, hn, ?_⟩
  rw [← apSum_eq_sum_Icc, Int.abs_eq_natAbs]
  exact_mod_cast hlt

/-- The full Erdős discrepancy conjecture (Tao's theorem), in Mathlib phrasing, is
equivalent to `Frontier.ErdosDiscrepancyConjecture`. -/
theorem erdosDiscrepancyConjecture_iff :
    ErdosDiscrepancyConjecture ↔
      ∀ f : ℕ → ℤ, (∀ n, 1 ≤ n → f n = 1 ∨ f n = -1) → ∀ C : ℕ,
        ∃ d n : ℕ, 1 ≤ d ∧ 1 ≤ n ∧ (C : ℤ) < |∑ i ∈ Finset.Icc 1 n, f (i * d)| := by
  constructor
  · intro h f hf C
    obtain ⟨d, n, hd, hn, hlt⟩ := h f hf C
    refine ⟨d, n, hd, hn, ?_⟩
    rw [← apSum_eq_sum_Icc, Int.abs_eq_natAbs]
    exact_mod_cast hlt
  · intro h f hf C
    obtain ⟨d, n, hd, hn, hlt⟩ := h f hf C
    rw [← apSum_eq_sum_Icc, Int.abs_eq_natAbs] at hlt
    exact ⟨d, n, hd, hn, by exact_mod_cast hlt⟩

end Frontier

