/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-- A comparison-based sorting algorithm for `n` elements, modelled as a binary
decision tree.  An internal node `node i j l r` compares the inputs at positions
`i` and `j`, descending into `l` if `a i < a j` and into `r` otherwise; a leaf
`leaf p` outputs the permutation `p`. -/
inductive CompTree (n : ℕ) : Type
  | leaf : Equiv.Perm (Fin n) → CompTree n
  | node : Fin n → Fin n → CompTree n → CompTree n → CompTree n
  deriving Inhabited

namespace CompTree

variable {n : ℕ}

/-- The worst-case number of comparisons performed by the algorithm, i.e. the
height of the decision tree. -/
def depth : CompTree n → ℕ
  | leaf _ => 0
  | node _ _ l r => max l.depth r.depth + 1

/-- Running the algorithm on the input `a i = σ i` (an arbitrary arrangement of
`n` distinct values, encoded by a permutation `σ`).  Only the outcomes of the
comparisons `a i < a j` are used. -/
def run : CompTree n → Equiv.Perm (Fin n) → Equiv.Perm (Fin n)
  | leaf p, _ => p
  | node i j l r, σ => if σ i < σ j then l.run σ else r.run σ

/-- The finite set of permutations appearing at the leaves of the tree. -/
def outputs : CompTree n → Finset (Equiv.Perm (Fin n))
  | leaf p => {p}
  | node _ _ l r => l.outputs ∪ r.outputs

theorem run_mem_outputs (t : CompTree n) (σ : Equiv.Perm (Fin n)) :
    t.run σ ∈ t.outputs := by
  induction t with
  | leaf p => simp [run, outputs]
  | node i j l r ihl ihr =>
      by_cases h : σ i < σ j <;> simp [run, outputs, h, ihl, ihr]

/-- A tree of height `d` has at most `2 ^ d` distinct leaf labels. -/
theorem card_outputs_le (t : CompTree n) : t.outputs.card ≤ 2 ^ t.depth := by
  induction t with
  | leaf p => simp [outputs, depth]
  | node i j l r ihl ihr =>
      refine (Finset.card_union_le _ _).trans ?_
      have hl : l.outputs.card ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : r.outputs.card ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      have hsum := Nat.add_le_add hl hr
      have : (2 : ℕ) ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth)
          = 2 ^ (max l.depth r.depth + 1) := by rw [pow_succ]; ring
      simpa [depth, this] using hsum

open Classical in
/-- The decision tree that successively asks all the comparisons in the list `L`,
keeping track of the set `P` of input arrangements still consistent with the
answers received so far, and finally outputs some consistent arrangement. -/
noncomputable def build : List (Fin n × Fin n) → (Equiv.Perm (Fin n) → Prop) → CompTree n
  | [], P => leaf (if h : ∃ σ, P σ then h.choose else 1)
  | (i, j) :: rest, P =>
      node i j (build rest (fun σ => P σ ∧ σ i < σ j))
        (build rest (fun σ => P σ ∧ ¬ σ i < σ j))

/-- On an input consistent with `P`, the tree `build L P` outputs an arrangement
that is consistent with `P` and agrees with the input on every comparison in `L`. -/
theorem run_build (L : List (Fin n × Fin n)) (P : Equiv.Perm (Fin n) → Prop)
    (σ : Equiv.Perm (Fin n)) (hP : P σ) :
    P ((build L P).run σ) ∧
      ∀ p ∈ L, ((build L P).run σ p.1 < (build L P).run σ p.2 ↔ σ p.1 < σ p.2) := by
  induction L generalizing P with
  | nil =>
      have hex : ∃ τ, P τ := ⟨σ, hP⟩
      refine ⟨?_, by simp⟩
      simpa [build, run, hex] using hex.choose_spec
  | cons p rest ih =>
      obtain ⟨i, j⟩ := p
      by_cases hij : σ i < σ j
      · obtain ⟨h1, h2⟩ := ih (fun τ => P τ ∧ τ i < τ j) ⟨hP, hij⟩
        have hrun : (build ((i, j) :: rest) P).run σ
            = (build rest (fun τ => P τ ∧ τ i < τ j)).run σ := by simp [build, run, hij]
        rw [hrun]
        refine ⟨h1.1, ?_⟩
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact iff_of_true h1.2 hij
        · exact h2 q hq
      · obtain ⟨h1, h2⟩ := ih (fun τ => P τ ∧ ¬ τ i < τ j) ⟨hP, hij⟩
        have hrun : (build ((i, j) :: rest) P).run σ
            = (build rest (fun τ => P τ ∧ ¬ τ i < τ j)).run σ := by simp [build, run, hij]
        rw [hrun]
        refine ⟨h1.1, ?_⟩
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact iff_of_false h1.2 hij
        · exact h2 q hq

end CompTree

/-- Two arrangements of `Fin n` that give the same answer to every comparison
are equal. -/
theorem perm_eq_of_lt_iff {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (h : ∀ i j, (τ i < τ j ↔ σ i < σ j)) : τ = σ := by
  let e : Fin n ≃o Fin n :=
    { toEquiv := σ.symm.trans τ
      map_rel_iff' := by
        intro a b
        simp only [Equiv.trans_apply]
        constructor
        · intro hab
          by_contra hlt
          push_neg at hlt
          have := (h (σ.symm b) (σ.symm a)).2 (by simpa using hlt)
          omega
        · intro hab
          rcases eq_or_lt_of_le hab with rfl | hab
          · exact le_refl _
          · exact le_of_lt ((h (σ.symm a) (σ.symm b)).2 (by simpa using hab)) }
  have he : ∀ a, τ (σ.symm a) = a := by
    intro a
    have := DFunLike.congr_fun (Subsingleton.elim e (OrderIso.refl (Fin n))) a
    simpa [e] using this
  exact Equiv.ext fun i => by simpa using he (σ i)

/-- The hypothesis of `CS.sorting_lb_4` is satisfiable: correct comparison sorts
of 4 elements do exist, so the lower bound below is not vacuous. -/
theorem exists_correct_tree (n : ℕ) :
    ∃ t : CompTree n, ∀ σ : Equiv.Perm (Fin n), t.run σ = σ := by
  classical
  refine ⟨CompTree.build (Finset.univ : Finset (Fin n × Fin n)).toList (fun _ => True), ?_⟩
  intro σ
  obtain ⟨-, h2⟩ :=
    CompTree.run_build (Finset.univ : Finset (Fin n × Fin n)).toList (fun _ => True) σ trivial
  exact perm_eq_of_lt_iff σ _ fun i j => h2 (i, j) (by simp)

/-- **Comparison-sorting lower bound for 4 elements.**
Any correct comparison sort of 4 elements — modelled as a binary decision tree
whose internal nodes compare two input positions and whose leaves output the
sorting permutation — performs at least `⌈log₂ (4!)⌉ = 5` comparisons in the
worst case. -/
theorem sorting_lb_4 (t : CompTree 4)
    (hcorrect : ∀ σ : Equiv.Perm (Fin 4), t.run σ = σ) :
    Nat.clog 2 (Nat.factorial 4) ≤ t.depth := by
  -- The tree must have at least `4! = 24` distinct leaves.
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin 4))) ⊆ t.outputs := by
    intro σ _
    have := t.run_mem_outputs σ
    rwa [hcorrect σ] at this
  have hcard : Nat.factorial 4 ≤ t.outputs.card := by
    have h1 : (Finset.univ : Finset (Equiv.Perm (Fin 4))).card = Nat.factorial 4 := by
      simp [Finset.card_univ, Fintype.card_perm]
    calc Nat.factorial 4 = (Finset.univ : Finset (Equiv.Perm (Fin 4))).card := h1.symm
      _ ≤ t.outputs.card := Finset.card_le_card hsub
  have h24 : Nat.factorial 4 ≤ 2 ^ t.depth := hcard.trans t.card_outputs_le
  -- Hence `depth ≥ ⌈log₂ 24⌉`.
  exact Nat.clog_le_of_le_pow h24

/-- `⌈log₂ (4!)⌉ = 5`, so the bound above says: at least 5 comparisons. -/
theorem clog_two_factorial_four : Nat.clog 2 (Nat.factorial 4) = 5 := by
  norm_num [Nat.factorial]

/-- Restatement of `CS.sorting_lb_4`: at least 5 comparisons are needed. -/
theorem sorting_lb_4_five (t : CompTree 4)
    (hcorrect : ∀ σ : Equiv.Perm (Fin 4), t.run σ = σ) : 5 ≤ t.depth := by
  have := sorting_lb_4 t hcorrect
  rwa [clog_two_factorial_four] at this

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

