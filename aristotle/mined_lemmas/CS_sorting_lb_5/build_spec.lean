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
