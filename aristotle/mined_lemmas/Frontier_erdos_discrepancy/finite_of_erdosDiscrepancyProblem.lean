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

