/-
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set TopologicalSpace

namespace Frontier

/-!
# Suslin's Problem

A *Suslin line* is a linear order, carrying its order topology, which satisfies the
**countable chain condition** (every family of pairwise disjoint nonempty open sets is
countable) but which is **not separable**.  Since every separable space is ccc
(`Frontier.isCCC_of_separableSpace`), a Suslin line is a space where the ccc fails to
imply separability.

*Suslin's Problem* asks whether every nonempty, ccc, densely ordered, unbounded,
conditionally complete linear order is order-isomorphic to `ℝ`; *Suslin's Hypothesis* is
the assertion that no Suslin line exists.

Both are independent of ZFC: Jensen's diamond principle `◊` implies that a Suslin line
exists, whereas `MA + ¬CH` implies Suslin's Hypothesis.  Consequently neither the
existence nor the nonexistence of a Suslin line is a theorem of ZFC, so neither can be
proved (nor refuted) in Lean's ambient set theory; the independence statements themselves
are assertions about models of ZFC rather than statements in the ZFC-like foundation Lean
formalises.

What *is* a theorem of ZFC, and is proved here, is the precise reduction of Suslin's
Problem to the nonexistence of a *Suslin continuum* (`Frontier.Suslin_line`), whose
mathematical core is Cantor's characterisation of the real line
(`Frontier.nonempty_orderIso_real`): a nonempty separable densely ordered unbounded
conditionally complete linear order is order-isomorphic to `ℝ`.  In particular Suslin's
Hypothesis implies the positive answer to Suslin's Problem, and conversely a positive
answer rules out all *complete* Suslin lines.

Mathlib has no notion of the countable chain condition, no notion of Suslin line, and no
characterisation of `ℝ` as an ordered topological space, so all of this is developed from
scratch here; the Mathlib inputs used are Cantor's isomorphism theorem for countable dense
linear orders (`Order.iso_of_countable_dense`), `exists_countable_dense`, and
`OrderIso.toHomeomorph`.
-/

/-- The **countable chain condition**: every family of pairwise disjoint nonempty open
sets is countable. -/

theorem cantorMap_surjective (hs : Dense s) (g : s ≃o ℚ) :
    Function.Surjective (cantorMap g) := by
  intro r
  set A : Set X := (fun d : s => (d : X)) '' {d : s | ((g d : ℚ) : ℝ) < r} with hA
  have hAne : A.Nonempty := by
    obtain ⟨q, hq⟩ := exists_rat_lt r
    exact ⟨_, ⟨g.symm q, by simpa using hq, rfl⟩⟩
  have hAbdd : BddAbove A := by
    obtain ⟨q, hq⟩ := exists_rat_gt r
    refine ⟨((g.symm q : s) : X), ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    have hlt : ((g d : ℚ) : ℝ) < ((q : ℚ) : ℝ) := lt_trans hd hq
    have hq2 : g d < q := by exact_mod_cast hlt
    have hd' : d < g.symm q := by
      have h := g.lt_iff_lt (x := d) (y := g.symm q)
      simp only [OrderIso.apply_symm_apply] at h
      exact h.mp hq2
    exact le_of_lt hd'
  set x : X := sSup A with hx
  refine ⟨x, ?_⟩
  have hle : cantorMap g x ≤ r := by
    refine csSup_le (cantorMap_setNonempty hs g x) ?_
    rintro _ ⟨d, hd, rfl⟩
    have hex : ∃ a ∈ A, (d : X) < a := by
      by_contra hcon
      push_neg at hcon
      exact absurd (csSup_le hAne hcon) (not_le.mpr hd)
    obtain ⟨a, ⟨d', hd', rfl⟩, hlt⟩ := hex
    have hdd' : d < d' := hlt
    have hcast : ((g d : ℚ) : ℝ) < ((g d' : ℚ) : ℝ) := by
      exact_mod_cast g.lt_iff_lt.mpr hdd'
    show ((g d : ℚ) : ℝ) ≤ r
    exact le_of_lt (lt_trans hcast hd')
  have hge : r ≤ cantorMap g x := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hcon
    obtain ⟨q', hq1', hq2'⟩ := exists_rat_btwn hq2
    have hmem : ((g.symm q' : s) : X) ∈ A := ⟨g.symm q', by simpa using hq2', rfl⟩
    have hxle : ((g.symm q' : s) : X) ≤ x := le_csSup hAbdd hmem
    have hqq'Q : q < q' := by exact_mod_cast hq1'
    have hqq' : (g.symm q : s) < g.symm q' := g.symm.lt_iff_lt.mpr hqq'Q
    have hqq'X : ((g.symm q : s) : X) < ((g.symm q' : s) : X) := hqq'
    have hlt : ((g.symm q : s) : X) < x := lt_of_lt_of_le hqq'X hxle
    have hle2 : ((q : ℚ) : ℝ) ≤ cantorMap g x := by
      have h := le_csSup (cantorMap_bddAbove hs g x) (Set.mem_image_of_mem
        (fun d : s => ((g d : ℚ) : ℝ)) hlt)
      simpa using h
    linarith
  linarith [hle, hge]

end Cantor

/-- **Cantor's characterisation of the real line.**  A nonempty separable densely ordered
unbounded conditionally complete linear order, with its order topology, is
order-isomorphic to `ℝ`. -/
