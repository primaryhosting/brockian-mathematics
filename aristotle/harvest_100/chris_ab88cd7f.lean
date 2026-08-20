import Mathlib

/-!
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- An input to a comparison sort of 5 elements is a "ranking": a permutation `s` of `Fin 5`
assigning to each position `i` its rank `s i`.  A comparison of positions `i` and `j` returns
`decide (s i < s j)`. -/
abbrev Rank := Equiv.Perm (Fin 5)

/-- A comparison-based decision tree for sorting 5 elements: an internal node compares two
positions and branches on the outcome, a leaf outputs a permutation (the claimed ranking). -/
inductive DTree : Type
  | leaf : Rank → DTree
  | node : Fin 5 → Fin 5 → DTree → DTree → DTree

/-- The worst-case number of comparisons performed by the tree. -/
def DTree.depth : DTree → ℕ
  | leaf _ => 0
  | node _ _ l r => max l.depth r.depth + 1

/-- Running the algorithm on an input ranking. -/
def DTree.run : DTree → Rank → Rank
  | leaf p, _ => p
  | node i j l r, s => if s i < s j then l.run s else r.run s

/-- A decision tree of depth `d` can produce at most `2 ^ d` distinct outputs. -/
lemma DTree.card_image_run_le (t : DTree) :
    (Finset.univ.image t.run).card ≤ 2 ^ t.depth := by
  induction t with
  | leaf p =>
      have : (Finset.univ.image (DTree.leaf p).run) = {p} := by
        ext x
        simp [DTree.run, eq_comm]
      simp [this, DTree.depth]
  | node i j l r ihl ihr =>
      have hsub : Finset.univ.image (DTree.node i j l r).run ⊆
          (Finset.univ.image l.run) ∪ (Finset.univ.image r.run) := by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨s, hs⟩ := hx
        simp only [DTree.run] at hs
        by_cases h : s i < s j
        · rw [if_pos h] at hs
          exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨s, Finset.mem_univ _, hs⟩)
        · rw [if_neg h] at hs
          exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨s, Finset.mem_univ _, hs⟩)
      calc (Finset.univ.image (DTree.node i j l r).run).card
          ≤ ((Finset.univ.image l.run) ∪ (Finset.univ.image r.run)).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.univ.image l.run).card + (Finset.univ.image r.run).card :=
            Finset.card_union_le _ _
        _ ≤ 2 ^ l.depth + 2 ^ r.depth := Nat.add_le_add ihl ihr
        _ ≤ 2 ^ (DTree.node i j l r).depth := by
            have h1 : (2:ℕ) ^ l.depth ≤ 2 ^ (max l.depth r.depth) :=
              Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
            have h2 : (2:ℕ) ^ r.depth ≤ 2 ^ (max l.depth r.depth) :=
              Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
            simp only [DTree.depth, pow_succ]
            omega

/-- **Comparison-sort lower bound for 5 elements.**
Any comparison-based decision tree that correctly sorts every arrangement of 5 elements
(i.e. outputs the true ranking on every input) makes at least `⌈log₂ (5!)⌉ = 7` comparisons
in the worst case. -/
theorem sorting_lb_5 (t : DTree) (hcorrect : ∀ s : Rank, t.run s = s) :
    Nat.clog 2 (Nat.factorial 5) ≤ t.depth := by
  have himg : Finset.univ.image t.run = (Finset.univ : Finset Rank) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact ⟨x, hcorrect x⟩
  have hcard : (Finset.univ : Finset Rank).card = 120 := by
    simp [Finset.card_univ, Fintype.card_perm]
    rfl
  have h120 : 120 ≤ 2 ^ t.depth := by
    have := t.card_image_run_le
    rw [himg, hcard] at this
    exact this
  have hd : 7 ≤ t.depth := by
    by_contra h
    push_neg at h
    have : (2:ℕ) ^ t.depth ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hclog : Nat.clog 2 (Nat.factorial 5) = 7 := by
    norm_num [Nat.factorial]
  rw [hclog]
  exact hd



/-- Explicit numeric form of the bound: at least `7` comparisons are needed, since
`⌈log₂ (5!)⌉ = ⌈log₂ 120⌉ = 7`. -/
theorem sorting_lb_5_seven (t : DTree) (hcorrect : ∀ s : Rank, t.run s = s) : 7 ≤ t.depth := by
  have h := sorting_lb_5 t hcorrect
  have hclog : Nat.clog 2 (Nat.factorial 5) = 7 := by norm_num [Nat.factorial]
  rwa [hclog] at h

/-! ## Non-vacuity: a correct comparison-sorting decision tree exists -/

/-- All 25 ordered pairs of positions. -/
def allPairs : List (Fin 5 × Fin 5) :=
  (List.finRange 5).flatMap (fun i => (List.finRange 5).map (fun j => (i, j)))

lemma mem_allPairs (i j : Fin 5) : (i, j) ∈ allPairs := by
  simp [allPairs, List.mem_flatMap]

/-- The list of answers to the comparisons in `L` on input `s`. -/
def ans (L : List (Fin 5 × Fin 5)) (s : Rank) : List Bool :=
  L.map (fun p => decide (s p.1 < s p.2))

/-- The complete decision tree asking exactly the comparisons in `L`, with leaves labelled
by `f` applied to the sequence of answers. -/
def full : List (Fin 5 × Fin 5) → (List Bool → Rank) → DTree
  | [], f => .leaf (f [])
  | p :: L, f => .node p.1 p.2 (full L (fun bs => f (true :: bs))) (full L (fun bs => f (false :: bs)))

lemma run_full (s : Rank) : ∀ (L : List (Fin 5 × Fin 5)) (f : List Bool → Rank),
    (full L f).run s = f (ans L s) := by
  intro L
  induction L with
  | nil => intro f; simp [full, DTree.run, ans]
  | cons p L ih =>
      intro f
      by_cases h : s p.1 < s p.2 <;> simp [full, DTree.run, ans, h, ih]

/-- Knowing the outcome of every comparison determines the input ranking. -/
lemma ans_allPairs_injective : Function.Injective (ans allPairs) := by
  intro s t hst
  have key : ∀ i j : Fin 5, s i < s j ↔ t i < t j := by
    intro i j
    have h := (List.map_inj_left.1 hst) (i, j) (mem_allPairs i j)
    simpa using h
  set e : Rank := t.symm.trans s with he_def
  have he : StrictMono (e : Fin 5 → Fin 5) := by
    intro a b hab
    have : t (t.symm a) < t (t.symm b) := by simpa using hab
    simpa [he_def] using (key (t.symm a) (t.symm b)).2 this
  have hesymm : StrictMono (e.symm : Fin 5 → Fin 5) := by
    intro a b hab
    by_contra hcon
    push_neg at hcon
    have := he.monotone hcon
    simp only [Equiv.apply_symm_apply] at this
    exact absurd hab (not_lt.2 this)
  have hfix : ∀ x : Fin 5, e x = x := by
    intro x
    have h1 : x ≤ e x := he.le_apply
    have h2 : x ≤ e.symm x := hesymm.le_apply
    have h3 : e x ≤ x := by
      have := he.monotone h2
      simpa using this
    exact le_antisymm h3 h1
  refine Equiv.ext fun y => ?_
  simpa [he_def] using hfix (t y)

open Classical in
/-- A leaf labelling: given the answers to all comparisons, output a ranking consistent
with them. -/
noncomputable def leafVal (bs : List Bool) : Rank :=
  if h : ∃ s : Rank, ans allPairs s = bs then h.choose else 1

/-- There **is** a comparison-based decision tree that sorts correctly, so the lower bound
above is not vacuous. -/
theorem exists_correct_tree : ∃ t : DTree, ∀ s : Rank, t.run s = s := by
  refine ⟨full allPairs leafVal, fun s => ?_⟩
  rw [run_full]
  have hex : ∃ s' : Rank, ans allPairs s' = ans allPairs s := ⟨s, rfl⟩
  rw [leafVal, dif_pos hex]
  exact ans_allPairs_injective hex.choose_spec

end CS

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

