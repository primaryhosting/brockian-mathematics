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

namespace CS

/-- A comparison-sorting algorithm on `n` elements, modelled as a binary decision tree.

The hidden input is a permutation `σ : Equiv.Perm (Fin n)`, thought of as the ranking of the
`n` input elements: element `i` has rank `σ i`.  An internal node `node i j l r` compares
elements `i` and `j`; the algorithm continues in `l` if `σ i < σ j` and in `r` otherwise.
A leaf reports the permutation the algorithm has decided the input is. -/
inductive CTree (n : ℕ) : Type
  | leaf (p : Equiv.Perm (Fin n)) : CTree n
  | node (i j : Fin n) (l r : CTree n) : CTree n
  deriving Inhabited

namespace CTree

variable {n : ℕ}

/-- The output of the algorithm `t` on the input ranking `σ`. -/
def run : CTree n → Equiv.Perm (Fin n) → Equiv.Perm (Fin n)
  | leaf p, _ => p
  | node i j l r, σ => if σ i < σ j then l.run σ else r.run σ

/-- The worst-case number of comparisons performed by `t`, i.e. the height of the tree. -/
def depth : CTree n → ℕ
  | leaf _ => 0
  | node _ _ l r => max l.depth r.depth + 1

/-- The list of all answers occurring at the leaves of `t`. -/
def leaves : CTree n → List (Equiv.Perm (Fin n))
  | leaf p => [p]
  | node _ _ l r => l.leaves ++ r.leaves

/-- A binary tree of height `d` has at most `2 ^ d` leaves. -/
theorem length_leaves_le (t : CTree n) : t.leaves.length ≤ 2 ^ t.depth := by
  induction t with
  | leaf p => simp [leaves, depth]
  | node i j l r ihl ihr =>
      have hl : l.leaves.length ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : r.leaves.length ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      simp only [leaves, depth, List.length_append, pow_succ]
      omega

/-- Every output of the algorithm is one of its leaf labels. -/
theorem run_mem_leaves (t : CTree n) (σ : Equiv.Perm (Fin n)) : t.run σ ∈ t.leaves := by
  induction t with
  | leaf p => simp [run, leaves]
  | node i j l r ihl ihr =>
      by_cases h : σ i < σ j <;> simp [run, leaves, h, ihl, ihr]

/-- Information-theoretic bound: a correct comparison sort on `n` elements must distinguish all
`n!` inputs, so `n! ≤ 2 ^ (worst-case number of comparisons)`. -/
theorem factorial_le_two_pow_depth (t : CTree n) (h : ∀ σ, t.run σ = σ) :
    Nat.factorial n ≤ 2 ^ t.depth := by
  classical
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin n))) ⊆ t.leaves.toFinset := by
    intro σ _
    simpa [List.mem_toFinset] using (h σ ▸ t.run_mem_leaves σ)
  have h1 : Nat.factorial n ≤ t.leaves.toFinset.card := by
    have := Finset.card_le_card hsub
    simpa [Fintype.card_perm] using this
  exact h1.trans <| (List.toFinset_card_le _).trans t.length_leaves_le

end CTree

/-- **Comparison-sorting lower bound for 5 elements.**
Any correct comparison sort of 5 elements (modelled as a binary decision tree whose internal
nodes compare two of the elements and whose leaves output a permutation) needs at least
`⌈log₂ (5!)⌉ = 7` comparisons in the worst case. -/
theorem sorting_lb_5 (t : CTree 5) (hcorrect : ∀ σ : Equiv.Perm (Fin 5), t.run σ = σ) :
    Nat.clog 2 (Nat.factorial 5) ≤ t.depth := by
  have h : Nat.factorial 5 ≤ 2 ^ t.depth := t.factorial_le_two_pow_depth hcorrect
  exact (Nat.clog_le_iff_le_pow (by norm_num)).2 h

/-- The bound in `CS.sorting_lb_5` is the number `7`. -/
theorem clog_two_factorial_five : Nat.clog 2 (Nat.factorial 5) = 7 := by
  norm_num [Nat.factorial]

/-- Restatement of `CS.sorting_lb_5`: at least `7` comparisons are needed. -/
theorem sorting_lb_5' (t : CTree 5) (hcorrect : ∀ σ : Equiv.Perm (Fin 5), t.run σ = σ) :
    7 ≤ t.depth := by
  simpa [clog_two_factorial_five] using sorting_lb_5 t hcorrect


/-! ### Non-vacuity: correct comparison sorts exist -/

namespace CTree

variable {n : ℕ}

/-- `build qs L` is the decision tree that resolves all the comparisons listed in `qs`
and then outputs the first candidate permutation of `L` consistent with all the answers. -/
def build : List (Fin n × Fin n) → List (Equiv.Perm (Fin n)) → CTree n
  | [], L => leaf (L.headD 1)
  | (i, j) :: qs, L =>
      node i j (build qs (L.filter (fun σ => decide (σ i < σ j))))
        (build qs (L.filter (fun σ => decide (σ j ≤ σ i))))

theorem build_spec :
    ∀ (qs : List (Fin n × Fin n)) (L : List (Equiv.Perm (Fin n))) (σ : Equiv.Perm (Fin n)),
      σ ∈ L → (build qs L).run σ ∈ L ∧
        ∀ q ∈ qs, ((build qs L).run σ q.1 < (build qs L).run σ q.2 ↔ σ q.1 < σ q.2) := by
  intro qs
  induction qs with
  | nil =>
      intro L σ hσ
      refine ⟨?_, by simp⟩
      cases L with
      | nil => simp at hσ
      | cons a t => simp [build, run]
  | cons q qs ih =>
      obtain ⟨i, j⟩ := q
      intro L σ hσ
      by_cases h : σ i < σ j
      · have hmem : σ ∈ L.filter (fun σ => decide (σ i < σ j)) := by
          simp [List.mem_filter, hσ, h]
        obtain ⟨h1, h2⟩ := ih _ σ hmem
        have hrun : (build ((i, j) :: qs) L).run σ =
            (build qs (L.filter (fun σ => decide (σ i < σ j)))).run σ := by
          simp [build, run, h]
        refine ⟨?_, ?_⟩
        · rw [hrun]; exact (List.mem_filter.1 h1).1
        · intro q hq
          rcases List.mem_cons.1 hq with rfl | hq'
          · have hlt := (List.mem_filter.1 h1).2
            simp only [decide_eq_true_eq] at hlt
            rw [hrun]
            exact iff_of_true hlt h
          · rw [hrun]; exact h2 q hq'
      · have hmem : σ ∈ L.filter (fun σ => decide (σ j ≤ σ i)) := by
          simp [List.mem_filter, hσ, not_lt.1 h]
        obtain ⟨h1, h2⟩ := ih _ σ hmem
        have hrun : (build ((i, j) :: qs) L).run σ =
            (build qs (L.filter (fun σ => decide (σ j ≤ σ i)))).run σ := by
          simp [build, run, h]
        refine ⟨?_, ?_⟩
        · rw [hrun]; exact (List.mem_filter.1 h1).1
        · intro q hq
          rcases List.mem_cons.1 hq with rfl | hq'
          · have hle := (List.mem_filter.1 h1).2
            simp only [decide_eq_true_eq] at hle
            rw [hrun]
            exact iff_of_false (not_lt.2 hle) h
          · rw [hrun]; exact h2 q hq'

end CTree

/-- Two permutations of `Fin n` inducing the same comparison answers are equal. -/
theorem perm_eq_of_lt_iff {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
    (h : ∀ i j : Fin n, τ i < τ j ↔ σ i < σ j) : τ = σ := by
  have hmono : StrictMono (fun x : Fin n => τ (σ.symm x)) := by
    intro a b hab
    have : σ (σ.symm a) < σ (σ.symm b) := by simpa using hab
    exact (h _ _).2 this
  have hid : ∀ x : Fin n, τ (σ.symm x) = x := by
    intro x
    have h1 : x ≤ τ (σ.symm x) := hmono.le_apply
    have h2 : τ (σ.symm x) ≤ x := hmono.dual.le_apply (β := (Fin n)ᵒᵈ)
    exact le_antisymm h2 h1
  refine Equiv.ext fun x => ?_
  simpa using hid (σ x)

/-- The model is not vacuous: for every `n` there is a correct comparison-sorting decision
tree on `n` elements. -/
theorem exists_correct_tree (n : ℕ) : ∃ t : CTree n, ∀ σ : Equiv.Perm (Fin n), t.run σ = σ := by
  classical
  refine ⟨CTree.build ((List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i, j))
      (Finset.univ : Finset (Equiv.Perm (Fin n))).toList, ?_⟩
  intro σ
  obtain ⟨-, h2⟩ := CTree.build_spec _ _ σ (Finset.mem_toList.2 (Finset.mem_univ σ))
  refine perm_eq_of_lt_iff (fun i j => h2 (i, j) ?_)
  exact List.mem_flatMap.2 ⟨i, by simp, by simp⟩

end CS

