/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

The Erdős discrepancy problem, solved by Terence Tao (2015), asserts that every
`±1`-valued sequence `f : ℕ → ℤ` has *unbounded* discrepancy along homogeneous
arithmetic progressions: for every bound `C` there are `d, n ≥ 1` with

  `|f d + f (2 d) + ⋯ + f (n d)| > C`.

This file formalises the statement (`Frontier.ErdosDiscrepancyProblem`) and proves
unconditionally the base case `C = 1`, in sharp form:

* `Frontier.erdos_discrepancy` : every `±1` sequence admits a homogeneous
  progression with `n * d ≤ 12` on which the partial sum has absolute value `> 1`;
* `Frontier.erdos_discrepancy_sharp` : the bound `12` cannot be lowered to `11`,
  witnessed by an explicit sequence of discrepancy `1` on all progressions inside
  `{1, …, 11}`.

It also contains a Lean-checked reduction: the infinite statement is equivalent to
its finite, uniform form `Frontier.FiniteEDP` (`erdosDiscrepancyProblem_of_finite`
and `finite_of_erdosDiscrepancyProblem`, the latter by compactness of the space of
`±1` sequences). The base case above is exactly `Frontier.FiniteEDP 1 12`.
-/

namespace Frontier

/-- The partial sum of `f` along the homogeneous arithmetic progression of common
difference `d`, taken over the first `n` terms: `f d + f (2 d) + ⋯ + f (n d)`. -/
def hapSum (f : ℕ → ℤ) (d n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, f (i * d)

/-- A `±1`-valued sequence (indices `≥ 1` are the relevant ones). -/
def IsPMOne (f : ℕ → ℤ) : Prop := ∀ n, 1 ≤ n → f n = 1 ∨ f n = -1

/-- `f` has unbounded discrepancy on homogeneous arithmetic progressions. -/
def HasUnboundedDiscrepancy (f : ℕ → ℤ) : Prop :=
  ∀ C : ℤ, ∃ d n : ℕ, 1 ≤ d ∧ 1 ≤ n ∧ C < |hapSum f d n|

/-- **The Erdős discrepancy problem** (theorem of Tao, 2015), as a statement:
every `±1` sequence has unbounded discrepancy on homogeneous arithmetic
progressions. -/
def ErdosDiscrepancyProblem : Prop :=
  ∀ f : ℕ → ℤ, IsPMOne f → HasUnboundedDiscrepancy f

/-- **Base case of the Erdős discrepancy problem** (`C = 1`), in sharp quantitative
form: for every `±1` sequence `f` there is a homogeneous arithmetic progression
`d, 2d, …, nd` with `n * d ≤ 12` along which the partial sum of `f` has absolute
value at least `2`. -/
theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsPMOne f) :
    ∃ d n : ℕ, 1 ≤ d ∧ 1 ≤ n ∧ n * d ≤ 12 ∧ 1 < |hapSum f d n| := by
  by_contra hcon
  push_neg at hcon
  have H : ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → n * d ≤ 12 →
      -1 ≤ hapSum f d n ∧ hapSum f d n ≤ 1 :=
    fun d n hd hn hnd => abs_le.mp (hcon d n hd hn hnd)
  have h12 := H 1 2 (by norm_num) (by norm_num) (by norm_num)
  have h14 := H 1 4 (by norm_num) (by norm_num) (by norm_num)
  have h16 := H 1 6 (by norm_num) (by norm_num) (by norm_num)
  have h18 := H 1 8 (by norm_num) (by norm_num) (by norm_num)
  have h1a := H 1 10 (by norm_num) (by norm_num) (by norm_num)
  have h22 := H 2 2 (by norm_num) (by norm_num) (by norm_num)
  have h32 := H 3 2 (by norm_num) (by norm_num) (by norm_num)
  have h34 := H 3 4 (by norm_num) (by norm_num) (by norm_num)
  have h42 := H 4 2 (by norm_num) (by norm_num) (by norm_num)
  have h52 := H 5 2 (by norm_num) (by norm_num) (by norm_num)
  have h62 := H 6 2 (by norm_num) (by norm_num) (by norm_num)
  simp only [hapSum] at h12 h14 h16 h18 h1a h22 h32 h34 h42 h52 h62
  simp [Finset.sum_Icc_succ_top] at h12 h14 h16 h18 h1a h22 h32 h34 h42 h52 h62
  have f1 := hf 1 (by norm_num)
  have f2 := hf 2 (by norm_num)
  have f3 := hf 3 (by norm_num)
  have f4 := hf 4 (by norm_num)
  have f5 := hf 5 (by norm_num)
  have f6 := hf 6 (by norm_num)
  have f7 := hf 7 (by norm_num)
  have f8 := hf 8 (by norm_num)
  have f9 := hf 9 (by norm_num)
  have f10 := hf 10 (by norm_num)
  have f12 := hf 12 (by norm_num)
  omega

/-- An explicit `±1` sequence of discrepancy `1` on all homogeneous progressions
contained in `{1, …, 11}`: `+ - - + - + + - - + +`, extended by `1`. -/
def sharpSeq : ℕ → ℤ := fun n => ([1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1] : List ℤ).getD (n - 1) 1

theorem sharpSeq_isPMOne : IsPMOne sharpSeq := by
  intro n _
  match n with
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => decide
  | (m + 12) => left; simp [sharpSeq, List.getD]

/-- Sharpness of the bound `12` in `Frontier.erdos_discrepancy`: there is a `±1`
sequence all of whose homogeneous progressions inside `{1, …, 11}` have partial
sums of absolute value at most `1`. -/
theorem erdos_discrepancy_sharp :
    ∃ f : ℕ → ℤ, IsPMOne f ∧
      ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → n * d ≤ 11 → |hapSum f d n| ≤ 1 := by
  refine ⟨sharpSeq, sharpSeq_isPMOne, ?_⟩
  have key : ∀ d ∈ Finset.Icc 1 11, ∀ n ∈ Finset.Icc 1 11,
      n * d ≤ 11 → |hapSum sharpSeq d n| ≤ 1 := by decide
  intro d n hd hn hnd
  have hdn : d ≤ n * d := Nat.le_mul_of_pos_left d hn
  have hnd' : n ≤ n * d := Nat.le_mul_of_pos_right n hd
  exact key d (Finset.mem_Icc.mpr ⟨hd, by omega⟩) n (Finset.mem_Icc.mpr ⟨hn, by omega⟩) hnd

/-!
## A Lean-checked reduction: the finite form is equivalent to the infinite form

`FiniteEDP C N` says that *every* `±1` sequence already exhibits discrepancy `> C`
inside the window `n * d ≤ N`. Trivially the finite form implies the infinite one;
the converse is a compactness argument, carried out below.
-/

/-- The finite (uniform, quantitative) form of the Erdős discrepancy problem:
every `±1` sequence has discrepancy exceeding `C` on some homogeneous progression
whose largest element is at most `N`. -/
def FiniteEDP (C : ℤ) (N : ℕ) : Prop :=
  ∀ f : ℕ → ℤ, IsPMOne f → ∃ d n : ℕ, 1 ≤ d ∧ 1 ≤ n ∧ n * d ≤ N ∧ C < |hapSum f d n|

/-- The base case, restated as the finite form at level `C = 1` with window `12`. -/
theorem finiteEDP_one : FiniteEDP 1 12 := fun f hf => erdos_discrepancy f hf

theorem hapSum_congr {f g : ℕ → ℤ} {d n : ℕ} (hd : 1 ≤ d) (h : ∀ k, 1 ≤ k → f k = g k) :
    hapSum f d n = hapSum g d n := by
  refine Finset.sum_congr rfl fun i hi => h _ ?_
  exact Nat.mul_pos (Finset.mem_Icc.mp hi).1 hd

theorem continuous_hapSum (d n : ℕ) : Continuous fun g : ℕ → ℤ => hapSum g d n :=
  continuous_finset_sum _ fun _ _ => continuous_apply _

/-- The finite form (for every `C`) implies the Erdős discrepancy problem. -/
theorem erdosDiscrepancyProblem_of_finite (H : ∀ C : ℤ, ∃ N, FiniteEDP C N) :
    ErdosDiscrepancyProblem := by
  intro f hf C
  obtain ⟨N, hN⟩ := H C
  obtain ⟨d, n, hd, hn, _, hlt⟩ := hN f hf
  exact ⟨d, n, hd, hn, hlt⟩

/-- Conversely, the Erdős discrepancy problem implies its finite form, by
compactness of the space of `±1` sequences. -/
theorem finite_of_erdosDiscrepancyProblem (H : ErdosDiscrepancyProblem) (C : ℤ) :
    ∃ N, FiniteEDP C N := by
  classical
  set S : Set (ℕ → ℤ) := Set.univ.pi fun _ => ({1, -1} : Set ℤ) with hSdef
  have hS : IsCompact S := isCompact_univ_pi fun _ => (Set.toFinite _).isCompact
  set U : ℕ → Set (ℕ → ℤ) :=
    fun N => {g | ∃ d n : ℕ, 1 ≤ d ∧ 1 ≤ n ∧ n * d ≤ N ∧ C < |hapSum g d n|} with hUdef
  have hUopen : ∀ N, IsOpen (U N) := by
    intro N
    rw [isOpen_iff_forall_mem_open]
    rintro g ⟨d, n, hd, hn, hdn, hlt⟩
    refine ⟨{h | C < |hapSum h d n|}, fun h hh => ⟨d, n, hd, hn, hdn, hh⟩, ?_, hlt⟩
    exact isOpen_lt continuous_const (continuous_hapSum d n).abs
  have hcover : S ⊆ ⋃ N, U N := by
    intro g hg
    have hgP : IsPMOne g := by
      intro k _
      have := hg k (Set.mem_univ k)
      simpa using this
    obtain ⟨d, n, hd, hn, hlt⟩ := H g hgP C
    exact Set.mem_iUnion.mpr ⟨n * d, d, n, hd, hn, le_rfl, hlt⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover U hUopen hcover
  refine ⟨t.sup id, ?_⟩
  intro f hf
  set g : ℕ → ℤ := fun k => if k = 0 then 1 else f k with hgdef
  have hgS : g ∈ S := by
    intro k _
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hgdef, hk]
    · have := hf k hk
      have hk0 : k ≠ 0 := by omega
      rcases this with h | h <;> simp [hgdef, hk0, h]
  obtain ⟨N, hNt, hgU⟩ := Set.mem_iUnion₂.mp (ht hgS)
  obtain ⟨d, n, hd, hn, hdn, hlt⟩ := hgU
  have hfg : hapSum f d n = hapSum g d n := by
    refine hapSum_congr hd fun k hk => ?_
    have hk0 : k ≠ 0 := by omega
    simp [hgdef, hk0]
  refine ⟨d, n, hd, hn, le_trans hdn (Finset.le_sup (f := id) hNt), ?_⟩
  rwa [hfg]

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

