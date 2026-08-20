/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: verified (axiom-clean: propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree sorting 4 elements.  A `leaf` outputs a
permutation (the claimed sorted order / ranking of the input), and a `node i j`
compares the input keys at positions `i` and `j` and branches accordingly. -/
inductive DTree where
  | leaf : Equiv.Perm (Fin 4) → DTree
  | node : Fin 4 → Fin 4 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by the tree. -/
def depth : DTree → ℕ
  | leaf _ => 0
  | node _ _ t f => max (depth t) (depth f) + 1

/-- The set of possible outputs of the tree. -/
def leaves : DTree → Finset (Equiv.Perm (Fin 4))
  | leaf p => {p}
  | node _ _ t f => leaves t ∪ leaves f

/-- Running the tree on the input whose key ranking is given by `σ`: the
comparison of positions `i` and `j` is answered by `σ i < σ j`. -/
def run : DTree → Equiv.Perm (Fin 4) → Equiv.Perm (Fin 4)
  | leaf p, _ => p
  | node i j t f, σ => if σ i < σ j then run t σ else run f σ

/-- A tree is a correct comparison sort if on every input it outputs the
ranking of that input. -/
def Correct (t : DTree) : Prop := ∀ σ : Equiv.Perm (Fin 4), run t σ = σ

theorem run_mem_leaves (t : DTree) (σ : Equiv.Perm (Fin 4)) : run t σ ∈ leaves t := by
  induction t with
  | leaf p => simp [run, leaves]
  | node i j t f iht ihf =>
      by_cases h : σ i < σ j <;> simp [run, leaves, h, iht, ihf]

theorem card_leaves_le (t : DTree) : (leaves t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf p => simp [leaves, depth]
  | node i j t f iht ihf =>
      refine le_trans (Finset.card_union_le _ _) ?_
      have h1 : (leaves t).card ≤ 2 ^ (max (depth t) (depth f)) :=
        iht.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have h2 : (leaves f).card ≤ 2 ^ (max (depth t) (depth f)) :=
        ihf.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc (leaves t).card + (leaves f).card
          ≤ 2 ^ (max (depth t) (depth f)) + 2 ^ (max (depth t) (depth f)) :=
            Nat.add_le_add h1 h2
        _ = 2 ^ depth (node i j t f) := by simp [depth, pow_succ]; ring

end DTree

/-- **Comparison-sort lower bound for 4 elements.**
Any correct comparison-based sorting decision tree for 4 elements must have
worst-case depth at least `⌈log₂ 4!⌉ = 5`. -/
theorem sorting_lb_4 (t : DTree) (h : DTree.Correct t) :
    Nat.clog 2 (Nat.factorial 4) ≤ t.depth ∧ 5 ≤ t.depth := by
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin 4))) ⊆ t.leaves := by
    intro σ _
    have := DTree.run_mem_leaves t σ
    rwa [h σ] at this
  have hcard : (24 : ℕ) ≤ (t.leaves).card := by
    have := Finset.card_le_card hsub
    simpa [Fintype.card_perm] using this
  have hle : Nat.factorial 4 ≤ 2 ^ t.depth :=
    le_trans (by norm_num [Nat.factorial]) (hcard.trans (DTree.card_leaves_le t))
  have hclog : Nat.clog 2 (Nat.factorial 4) ≤ t.depth :=
    (Nat.clog_le_iff_le_pow (by norm_num)).2 hle
  refine ⟨hclog, ?_⟩
  have : Nat.clog 2 (Nat.factorial 4) = 5 := by norm_num [Nat.factorial]
  omega

/-! ### Non-vacuity: correct comparison sorts do exist -/

/-- A permutation of `Fin n` is determined by the relative order of its values. -/
theorem perm_eq_of_lt_iff {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (h : ∀ i j, σ i < σ j ↔ τ i < τ j) : σ = τ := by
  have key : ∀ a b : Equiv.Perm (Fin n), (∀ i j, a i < a j ↔ b i < b j) →
      ∀ x, x ≤ b (a.symm x) := by
    intro a b hab
    have hmono : StrictMono (a.symm.trans b) := by
      intro x y hxy
      have hx : a (a.symm x) < a (a.symm y) := by simpa using hxy
      simpa using (hab (a.symm x) (a.symm y)).1 hx
    intro x
    simpa using hmono.le_apply (x := x)
  have h1 := key σ τ h
  have h2 := key τ σ fun i j => (h i j).symm
  refine Equiv.ext fun x => ?_
  have a1 : σ x ≤ τ x := by simpa using h1 (σ x)
  have a2 : τ x ≤ σ x := by simpa using h2 (τ x)
  exact le_antisymm a1 a2

/-- All pairs of indices. -/
def allPairs : List (Fin 4 × Fin 4) :=
  (List.finRange 4).flatMap fun i => (List.finRange 4).map fun j => (i, j)

theorem mem_allPairs : ∀ p : Fin 4 × Fin 4, p ∈ allPairs := by decide

/-- The brute-force decision tree: perform every comparison in `L`, restricting
the set `ps` of candidate answers accordingly, and output a surviving candidate. -/
noncomputable def buildT : List (Fin 4 × Fin 4) → Finset (Equiv.Perm (Fin 4)) → DTree
  | [], ps => .leaf (if h : ps.Nonempty then h.choose else 1)
  | (i, j) :: rest, ps =>
      .node i j (buildT rest (ps.filter fun τ => τ i < τ j))
        (buildT rest (ps.filter fun τ => ¬ τ i < τ j))

theorem buildT_spec : ∀ (L : List (Fin 4 × Fin 4)) (ps : Finset (Equiv.Perm (Fin 4)))
    (σ : Equiv.Perm (Fin 4)), σ ∈ ps →
    DTree.run (buildT L ps) σ ∈ ps ∧
      ∀ p ∈ L, (DTree.run (buildT L ps) σ p.1 < DTree.run (buildT L ps) σ p.2 ↔ σ p.1 < σ p.2) := by
  intro L
  induction L with
  | nil =>
      intro ps σ hσ
      refine ⟨?_, by simp⟩
      have hne : ps.Nonempty := ⟨σ, hσ⟩
      simp only [buildT, DTree.run, dif_pos hne]
      exact hne.choose_spec
  | cons p rest ih =>
      obtain ⟨i, j⟩ := p
      intro ps σ hσ
      by_cases hc : σ i < σ j
      · have hmem : σ ∈ ps.filter fun τ => τ i < τ j := by
          simp only [Finset.mem_filter]; exact ⟨hσ, hc⟩
        obtain ⟨h1, h2⟩ := ih (ps.filter fun τ => τ i < τ j) σ hmem
        have hrun : DTree.run (buildT ((i, j) :: rest) ps) σ
            = DTree.run (buildT rest (ps.filter fun τ => τ i < τ j)) σ := by
          simp [buildT, DTree.run, hc]
        rw [Finset.mem_filter] at h1
        refine ⟨by rw [hrun]; exact h1.1, ?_⟩
        intro q hq
        rcases List.mem_cons.1 hq with hq | hq
        · subst hq
          rw [hrun]
          exact iff_of_true h1.2 hc
        · rw [hrun]; exact h2 q hq
      · have hmem : σ ∈ ps.filter fun τ => ¬ τ i < τ j := by
          simp only [Finset.mem_filter]; exact ⟨hσ, hc⟩
        obtain ⟨h1, h2⟩ := ih (ps.filter fun τ => ¬ τ i < τ j) σ hmem
        have hrun : DTree.run (buildT ((i, j) :: rest) ps) σ
            = DTree.run (buildT rest (ps.filter fun τ => ¬ τ i < τ j)) σ := by
          simp [buildT, DTree.run, hc]
        rw [Finset.mem_filter] at h1
        refine ⟨by rw [hrun]; exact h1.1, ?_⟩
        intro q hq
        rcases List.mem_cons.1 hq with hq | hq
        · subst hq
          rw [hrun]
          exact iff_of_false h1.2 hc
        · rw [hrun]; exact h2 q hq

/-- Correct comparison sorts of 4 elements exist, so the lower bound above is
not vacuous. -/
theorem exists_correct : ∃ t : DTree, DTree.Correct t := by
  refine ⟨buildT allPairs Finset.univ, fun σ => ?_⟩
  have h := (buildT_spec allPairs Finset.univ σ (Finset.mem_univ σ)).2
  exact perm_eq_of_lt_iff _ _ fun i j => h (i, j) (mem_allPairs (i, j))

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

