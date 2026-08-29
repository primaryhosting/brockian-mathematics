import Mathlib
/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Filter Set

private lemma fin2_eq_one_iff : ∀ x : Fin 2, x = 1 ↔ x ≠ 0 := by decide

/-- For any two-valued function on `ℕ` and any ultrafilter `U`, one of the two fibres
belongs to `U`. -/
private lemma exists_colour_mem (U : Ultrafilter ℕ) (f : ℕ → Fin 2) :
    ∃ j : Fin 2, {n | f n = j} ∈ U := by
  by_cases h : {n | f n = 0} ∈ U
  · exact ⟨0, h⟩
  · refine ⟨1, ?_⟩
    have hset : {n | f n = 1} = {n | f n = 0}ᶜ := by
      ext n
      simp only [mem_setOf_eq, mem_compl_iff, fin2_eq_one_iff, ne_eq]
    rw [hset]
    exact Ultrafilter.compl_mem_iff_notMem.2 h

/-- Choose an element of a set (junk value `0` if empty). -/
private noncomputable def pick (T : Set ℕ) : ℕ :=
  open Classical in if h : T.Nonempty then h.choose else 0

private lemma pick_mem {T : Set ℕ} (h : T.Nonempty) : pick T ∈ T := by
  classical
  rw [pick, dif_pos h]
  exact h.choose_spec

/-- One step of the construction: from a pair `(last element, remaining set)`,
pick a new element of the remaining set beyond `last`, and shrink the set to those
points joined to the new element with colour `i`. -/
private noncomputable def step (c : ℕ → ℕ → Fin 2) (i : Fin 2) (p : ℕ × Set ℕ) : ℕ × Set ℕ :=
  (pick (p.2 ∩ {m | p.1 < m}), p.2 ∩ {m | c (pick (p.2 ∩ {m | p.1 < m})) m = i})

private noncomputable def st (c : ℕ → ℕ → Fin 2) (i : Fin 2) (A : Set ℕ) : ℕ → ℕ × Set ℕ
  | 0 => (0, A)
  | k + 1 => step c i (st c i A k)

variable {c : ℕ → ℕ → Fin 2} {i : Fin 2} {A : Set ℕ} {U : Ultrafilter ℕ}

private lemma st_invariant (hcof : ∀ l : ℕ, {m | l < m} ∈ U) (hA : A ∈ U)
    (hAi : ∀ n ∈ A, {m | c n m = i} ∈ U) :
    ∀ k, (st c i A k).2 ∈ U ∧ (st c i A k).2 ⊆ A := by
  intro k
  induction k with
  | zero => exact ⟨hA, subset_rfl⟩
  | succ k ih =>
      obtain ⟨hmem, hsub⟩ := ih
      have hU : ((st c i A k).2 ∩ {m | (st c i A k).1 < m}) ∈ U := inter_mem hmem (hcof _)
      have hn : pick ((st c i A k).2 ∩ {m | (st c i A k).1 < m}) ∈
          (st c i A k).2 ∩ {m | (st c i A k).1 < m} := pick_mem (Filter.nonempty_of_mem hU)
      have hnA : pick ((st c i A k).2 ∩ {m | (st c i A k).1 < m}) ∈ A := hsub hn.1
      refine ⟨?_, ?_⟩
      · simp only [st, step]
        exact inter_mem hmem (hAi _ hnA)
      · simp only [st, step]
        exact inter_subset_left.trans hsub

private lemma st_step_mem (hcof : ∀ l : ℕ, {m | l < m} ∈ U) (hA : A ∈ U)
    (hAi : ∀ n ∈ A, {m | c n m = i} ∈ U) (k : ℕ) :
    (st c i A (k + 1)).1 ∈ (st c i A k).2 ∧ (st c i A k).1 < (st c i A (k + 1)).1 := by
  obtain ⟨hmem, _⟩ := st_invariant hcof hA hAi k
  have hn : pick ((st c i A k).2 ∩ {m | (st c i A k).1 < m}) ∈
      (st c i A k).2 ∩ {m | (st c i A k).1 < m} :=
    pick_mem (Filter.nonempty_of_mem (inter_mem hmem (hcof _)))
  exact ⟨hn.1, hn.2⟩

private lemma st_antitone {j k : ℕ} (h : j ≤ k) : (st c i A k).2 ⊆ (st c i A j).2 := by
  induction k, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ k _ ih =>
      refine subset_trans ?_ ih
      intro m hm
      simp only [st, step] at hm
      exact hm.1

private lemma st_colour (k : ℕ) :
    (st c i A (k + 1)).2 ⊆ {m | c ((st c i A (k + 1)).1) m = i} := by
  intro m hm
  simp only [st, step] at hm ⊢
  exact hm.2

/-- **Infinite Ramsey theorem** for pairs and two colours: for every 2-colouring `c`
of the (unordered) pairs of natural numbers there is an infinite set `S ⊆ ℕ` and a
colour `i` such that every pair from `S` receives colour `i`. -/
theorem infinite_ramsey (c : ℕ → ℕ → Fin 2) :
    ∃ (S : Set ℕ) (i : Fin 2), S.Infinite ∧ ∀ x ∈ S, ∀ y ∈ S, x < y → c x y = i := by
  classical
  -- a nonprincipal ultrafilter on `ℕ`
  set U : Ultrafilter ℕ := hyperfilter ℕ
  have hcof : ∀ s : Set ℕ, s ∈ (cofinite : Filter ℕ) → s ∈ U := fun _ hs =>
    Filter.hyperfilter_le_cofinite hs
  have hgt : ∀ l : ℕ, {m : ℕ | l < m} ∈ U := by
    intro l
    refine hcof _ ?_
    rw [Nat.cofinite_eq_atTop]
    exact eventually_gt_atTop l
  -- the `U`-majority colour seen from each point
  choose d hdU using fun n : ℕ => exists_colour_mem U (c n)
  -- the `U`-majority value of `d`
  obtain ⟨i, hA⟩ := exists_colour_mem U d
  set A : Set ℕ := {n | d n = i}
  have hAi : ∀ n ∈ A, {m | c n m = i} ∈ U := by
    intro n hn
    have : d n = i := hn
    rw [← this]
    exact hdU n
  have hstep := st_step_mem hgt hA hAi
  set a : ℕ → ℕ := fun k => (st c i A (k + 1)).1
  have hmono : StrictMono a := strictMono_nat_of_lt_succ fun k => (hstep (k + 1)).2
  have hcol : ∀ j k : ℕ, j < k → c (a j) (a k) = i := by
    intro j k hjk
    have h1 : a k ∈ (st c i A k).2 := (hstep k).1
    have h2 : (st c i A k).2 ⊆ (st c i A (j + 1)).2 := st_antitone hjk
    exact st_colour (c := c) (i := i) (A := A) j (h2 h1)
  refine ⟨Set.range a, i, Set.infinite_range_of_injective hmono.injective, ?_⟩
  rintro x ⟨j, rfl⟩ y ⟨k, rfl⟩ hxy
  exact hcol j k (hmono.lt_iff_lt.1 hxy)

/-- **Infinite Ramsey theorem**, stated for genuinely unordered pairs: every 2-colouring
of `[ℕ]²`, viewed as a colouring of the unordered pairs `s(x, y)` with `x ≠ y`, has an
infinite monochromatic set. -/
theorem infinite_ramsey_sym2 (c : Sym2 ℕ → Fin 2) :
    ∃ (S : Set ℕ) (i : Fin 2), S.Infinite ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c s(x, y) = i := by
  obtain ⟨S, i, hS, hmono⟩ := infinite_ramsey fun x y => c s(x, y)
  refine ⟨S, i, hS, fun x hx y hy hxy => ?_⟩
  rcases lt_or_gt_of_ne hxy with h | h
  · exact hmono x hx y hy h
  · rw [Sym2.eq_swap]
    exact hmono y hy x hx h

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

