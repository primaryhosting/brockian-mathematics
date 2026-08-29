/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Mathlib (as of this version) contains no infinite Ramsey theorem — searching for `Ramsey`
turns up only `Mathlib/Combinatorics/Hindman.lean` and `Mathlib/Combinatorics/HalesJewett.lean`,
where the word occurs in comments.  So we prove it from scratch, using the classical
ultrafilter argument based on `Filter.hyperfilter`.
-/

namespace Frontier

open Filter Set

noncomputable section

/-- A choice of element of a set of naturals (junk value `0` for the empty set). -/
private def pick (B : Set ℕ) : ℕ := if h : B.Nonempty then h.choose else 0

private lemma pick_mem {B : Set ℕ} (h : B.Nonempty) : pick B ∈ B := by
  rw [pick, dif_pos h]
  exact h.choose_spec

/-- The `hyperfilter`-majority colour of the pairs `{n, m}` as `m` varies. -/
private def ufColor (C : ℕ → ℕ → Bool) (n : ℕ) : Bool :=
  if {m | C n m = true} ∈ hyperfilter ℕ then true else false

private lemma ufColor_mem (C : ℕ → ℕ → Bool) (n : ℕ) :
    {m | C n m = ufColor C n} ∈ hyperfilter ℕ := by
  by_cases h : {m | C n m = true} ∈ hyperfilter ℕ
  · simpa [ufColor, h] using h
  · have hc : {m | C n m = true}ᶜ ∈ hyperfilter ℕ :=
      (Ultrafilter.compl_mem_iff_notMem).2 h
    have he : {m | C n m = false} = {m | C n m = true}ᶜ := by
      ext m; simp [Bool.eq_false_iff]
    simpa [ufColor, h, he] using hc

variable (C : ℕ → ℕ → Bool) (c0 : Bool)

/-- The decreasing sequence of large sets used to build the monochromatic set. -/
private def ramseySeq : ℕ → Set ℕ
  | 0 => {n | ufColor C n = c0}
  | k + 1 =>
      (ramseySeq k) ∩ Ioi (pick (ramseySeq k)) ∩ {m | C (pick (ramseySeq k)) m = c0}

/-- The `k`-th element of the monochromatic set. -/
private def ramseyElt (k : ℕ) : ℕ := pick (ramseySeq C c0 k)

private lemma ramseySeq_succ_subset (k : ℕ) : ramseySeq C c0 (k + 1) ⊆ ramseySeq C c0 k := by
  intro x hx
  exact hx.1.1

private lemma ramseySeq_antitone {i j : ℕ} (h : i ≤ j) :
    ramseySeq C c0 j ⊆ ramseySeq C c0 i := by
  induction j with
  | zero => simpa using (Nat.le_zero.1 h) ▸ subset_rfl
  | succ n ih =>
      rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · exact (ramseySeq_succ_subset C c0 n).trans (ih (Nat.lt_succ_iff.1 hlt))
      · have : i = n + 1 := le_antisymm h hge
        subst this; exact subset_rfl

private lemma ramseySeq_mem (h0 : {n | ufColor C n = c0} ∈ hyperfilter ℕ) (k : ℕ) :
    ramseySeq C c0 k ∈ hyperfilter ℕ := by
  induction k with
  | zero => simpa [ramseySeq] using h0
  | succ n ih =>
      have hne : (ramseySeq C c0 n).Nonempty := Ultrafilter.nonempty_of_mem ih
      have hx : pick (ramseySeq C c0 n) ∈ ramseySeq C c0 n := pick_mem hne
      set x := pick (ramseySeq C c0 n) with hxdef
      have hx0 : x ∈ ramseySeq C c0 0 := ramseySeq_antitone C c0 (Nat.zero_le n) hx
      have hcol : ufColor C x = c0 := hx0
      have h1 : Ioi x ∈ hyperfilter ℕ := by
        refine mem_hyperfilter_of_finite_compl ?_
        simpa using (Set.finite_Iic x)
      have h2 : {m | C x m = c0} ∈ hyperfilter ℕ := by
        have := ufColor_mem C x
        rwa [hcol] at this
      have : ramseySeq C c0 n ∩ Ioi x ∩ {m | C x m = c0} ∈ hyperfilter ℕ :=
        Ultrafilter.inter_mem (Ultrafilter.inter_mem ih h1) h2
      simpa [ramseySeq, ← hxdef] using this

private lemma ramseyElt_mem (h0 : {n | ufColor C n = c0} ∈ hyperfilter ℕ) (k : ℕ) :
    ramseyElt C c0 k ∈ ramseySeq C c0 k :=
  pick_mem (Ultrafilter.nonempty_of_mem (ramseySeq_mem C c0 h0 k))

private lemma ramseyElt_lt (h0 : {n | ufColor C n = c0} ∈ hyperfilter ℕ) (k : ℕ) :
    ramseyElt C c0 k < ramseyElt C c0 (k + 1) := by
  have h := ramseyElt_mem C c0 h0 (k + 1)
  have : ramseyElt C c0 (k + 1) ∈ Ioi (pick (ramseySeq C c0 k)) := h.1.2
  simpa [ramseyElt] using this

private lemma ramseyElt_strictMono (h0 : {n | ufColor C n = c0} ∈ hyperfilter ℕ) :
    StrictMono (ramseyElt C c0) :=
  strictMono_nat_of_lt_succ (ramseyElt_lt C c0 h0)

private lemma ramseyElt_color (h0 : {n | ufColor C n = c0} ∈ hyperfilter ℕ) {i j : ℕ}
    (hij : i < j) : C (ramseyElt C c0 i) (ramseyElt C c0 j) = c0 := by
  have hj : ramseyElt C c0 j ∈ ramseySeq C c0 (i + 1) :=
    ramseySeq_antitone C c0 hij (ramseyElt_mem C c0 h0 j)
  exact hj.2

end

/-- **Infinite Ramsey theorem** for pairs and two colours: for every colouring `C` of the
pairs `{i, j}` of naturals (represented by the values `C i j` for `i < j`) by two colours,
there is an infinite set `S ⊆ ℕ` and a colour `c` such that every pair from `S` has
colour `c`. -/
theorem infinite_ramsey (C : ℕ → ℕ → Bool) :
    ∃ (S : Set ℕ) (c : Bool), S.Infinite ∧ ∀ i ∈ S, ∀ j ∈ S, i < j → C i j = c := by
  classical
  -- Choose the colour `c0` whose set of `hyperfilter`-majority vertices is large.
  obtain ⟨c0, h0⟩ : ∃ c0 : Bool, {n | ufColor C n = c0} ∈ hyperfilter ℕ := by
    rcases Ultrafilter.mem_or_compl_mem (hyperfilter ℕ) {n | ufColor C n = true} with h | h
    · exact ⟨true, h⟩
    · refine ⟨false, ?_⟩
      have he : {n | ufColor C n = false} = {n | ufColor C n = true}ᶜ := by
        ext n; simp [Bool.eq_false_iff]
      rw [he]; exact h
  refine ⟨Set.range (ramseyElt C c0), c0, ?_, ?_⟩
  · exact Set.infinite_range_of_injective (ramseyElt_strictMono C c0 h0).injective
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hlt
    have hij : i < j := by
      by_contra hle
      exact absurd ((ramseyElt_strictMono C c0 h0).le_iff_le.2 (not_lt.1 hle)) (not_le.2 hlt)
    exact ramseyElt_color C c0 h0 hij

/-- Symmetric version: for a symmetric two-colouring of pairs of naturals there is an
infinite monochromatic set. -/
theorem infinite_ramsey_symm (C : ℕ → ℕ → Bool) (hsymm : ∀ i j, C i j = C j i) :
    ∃ (S : Set ℕ) (c : Bool), S.Infinite ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → C i j = c := by
  obtain ⟨S, c, hinf, hmono⟩ := infinite_ramsey C
  refine ⟨S, c, hinf, ?_⟩
  intro i hi j hj hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hmono i hi j hj h
  · rw [hsymm]; exact hmono j hj i hi h

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

