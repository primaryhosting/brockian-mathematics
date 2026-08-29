/-
/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

namespace Frontier

open Filter Set

/-- A fixed nonprincipal ultrafilter on `ℕ`: an ultrafilter refining the cofinite filter. -/
noncomputable def ramseyUF : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite

lemma ramseyUF_le_cofinite : (ramseyUF : Filter ℕ) ≤ Filter.cofinite :=
  Ultrafilter.of_le _

lemma Ioi_mem_ramseyUF (x : ℕ) : Set.Ioi x ∈ ramseyUF :=
  ramseyUF_le_cofinite (by rw [Nat.cofinite_eq_atTop]; exact Filter.Ioi_mem_atTop x)

/-- The "ultrafilter colour" of a vertex `x`: the colour `b` such that
`{y | c x y = b}` belongs to the ultrafilter. -/
open scoped Classical in
noncomputable def ufColor (c : ℕ → ℕ → Bool) (x : ℕ) : Bool :=
  if {y | c x y = true} ∈ ramseyUF then true else false

lemma ufColor_mem (c : ℕ → ℕ → Bool) (x : ℕ) :
    {y | c x y = ufColor c x} ∈ ramseyUF := by
  classical
  rw [ufColor]
  split_ifs with h
  · simpa using h
  · have h2 : {y | c x y = true}ᶜ ∈ ramseyUF := Ultrafilter.compl_mem_iff_notMem.mpr h
    have : {y | c x y = false} = {y | c x y = true}ᶜ := by
      ext y; simp
    rw [this]
    exact h2

/-- Pick an element of a set (junk value `0` if empty). -/
open scoped Classical in
noncomputable def pickElem (T : Set ℕ) : ℕ := if h : T.Nonempty then h.choose else 0

lemma pickElem_mem {T : Set ℕ} (h : T.Nonempty) : pickElem T ∈ T := by
  classical
  rw [pickElem, dif_pos h]
  exact h.choose_spec

/-- One step of the construction: shrink `T` to the elements above `pickElem T` which
are joined to it in colour `ufColor c (pickElem T)`. -/
noncomputable def ramseyStep (c : ℕ → ℕ → Bool) (T : Set ℕ) : Set ℕ :=
  T ∩ Set.Ioi (pickElem T) ∩ {y | c (pickElem T) y = ufColor c (pickElem T)}

/-- The decreasing sequence of ultrafilter sets. -/
noncomputable def ramseySet (c : ℕ → ℕ → Bool) (n : ℕ) : Set ℕ :=
  (ramseyStep c)^[n] Set.univ

/-- The constructed increasing sequence of vertices. -/
noncomputable def ramseySeq (c : ℕ → ℕ → Bool) (n : ℕ) : ℕ := pickElem (ramseySet c n)

lemma ramseySet_succ (c : ℕ → ℕ → Bool) (n : ℕ) :
    ramseySet c (n + 1) = ramseyStep c (ramseySet c n) := by
  simp [ramseySet, Function.iterate_succ_apply']

lemma ramseySet_mem (c : ℕ → ℕ → Bool) : ∀ n, ramseySet c n ∈ ramseyUF := by
  intro n
  induction n with
  | zero =>
      rw [ramseySet]
      simpa using Filter.univ_mem
  | succ n ih =>
      rw [ramseySet_succ, ramseyStep]
      exact Filter.inter_mem (Filter.inter_mem ih (Ioi_mem_ramseyUF _)) (ufColor_mem c _)

lemma ramseySeq_mem (c : ℕ → ℕ → Bool) (n : ℕ) : ramseySeq c n ∈ ramseySet c n :=
  pickElem_mem (Ultrafilter.nonempty_of_mem (ramseySet_mem c n))

lemma ramseySet_antitone (c : ℕ → ℕ → Bool) {m n : ℕ} (h : m ≤ n) :
    ramseySet c n ⊆ ramseySet c m := by
  induction n with
  | zero => simp_all
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hm | hm
      · have : ramseySet c (n + 1) ⊆ ramseySet c n := by
          rw [ramseySet_succ, ramseyStep]
          exact fun y hy => hy.1.1
        exact this.trans (ih (Nat.lt_succ_iff.mp hm))
      · have : m = n + 1 := le_antisymm h hm
        subst this; exact subset_rfl

lemma ramseySeq_lt (c : ℕ → ℕ → Bool) {m n : ℕ} (h : m < n) :
    ramseySeq c m < ramseySeq c n := by
  have hmem : ramseySeq c n ∈ ramseySet c (m + 1) :=
    ramseySet_antitone c h (ramseySeq_mem c n)
  rw [ramseySet_succ, ramseyStep] at hmem
  exact hmem.1.2

lemma ramseySeq_color (c : ℕ → ℕ → Bool) {m n : ℕ} (h : m < n) :
    c (ramseySeq c m) (ramseySeq c n) = ufColor c (ramseySeq c m) := by
  have hmem : ramseySeq c n ∈ ramseySet c (m + 1) :=
    ramseySet_antitone c h (ramseySeq_mem c n)
  rw [ramseySet_succ, ramseyStep] at hmem
  exact hmem.2

lemma ramseySeq_strictMono (c : ℕ → ℕ → Bool) : StrictMono (ramseySeq c) :=
  fun _ _ h => ramseySeq_lt c h

/-- **Infinite Ramsey theorem** for pairs and two colours: for every colouring
`c : ℕ → ℕ → Bool` of the unordered pairs of natural numbers (a pair `{x, y}` with
`x < y` receiving the colour `c x y`) there is an infinite set `S ⊆ ℕ` all of whose
pairs receive the same colour `b`. -/
theorem infinite_ramsey (c : ℕ → ℕ → Bool) :
    ∃ (S : Set ℕ) (b : Bool), S.Infinite ∧ ∀ x ∈ S, ∀ y ∈ S, x < y → c x y = b := by
  -- one of the two colour classes of indices is infinite
  have huniv : {n : ℕ | ufColor c (ramseySeq c n) = true} ∪
      {n : ℕ | ufColor c (ramseySeq c n) = false} = Set.univ := by
    ext n
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    cases ufColor c (ramseySeq c n) <;> simp
  have hinf : ∃ b : Bool, {n : ℕ | ufColor c (ramseySeq c n) = b}.Infinite := by
    by_contra hcon
    push_neg at hcon
    have h1 := hcon true
    have h2 := hcon false
    have : (Set.univ : Set ℕ).Finite := huniv ▸ h1.union h2
    exact Set.infinite_univ this
  obtain ⟨b, hb⟩ := hinf
  refine ⟨ramseySeq c '' {n : ℕ | ufColor c (ramseySeq c n) = b}, b, ?_, ?_⟩
  · exact hb.image ((ramseySeq_strictMono c).injective.injOn)
  · rintro x ⟨m, hm, rfl⟩ y ⟨n, hn, rfl⟩ hlt
    have hmn : m < n := by
      by_contra hge
      push_neg at hge
      exact absurd hlt (not_lt.mpr ((ramseySeq_strictMono c).monotone hge))
    rw [ramseySeq_color c hmn]
    exact hm

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

