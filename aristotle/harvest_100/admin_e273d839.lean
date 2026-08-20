/-
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sorting Lb 5

A comparison sort on `5` elements is modelled as a binary comparison decision tree:
each internal node asks a comparison `x i < x j` between two of the five input
positions, and each leaf outputs the permutation describing the sorted order.

The input is encoded by a permutation `σ : Equiv.Perm (Fin 5)` giving the rank
`σ i` of the element in position `i`; the comparison at a node `(i, j)` is
answered by `σ i < σ j`.  Correctness means the tree outputs `σ` on input `σ`.

The main result `CS.sorting_lb_5` says that the depth (worst-case number of
comparisons) of any correct tree is at least `⌈log₂ (5!)⌉ = 7`.
-/

namespace CS

/-- Rankings of the five inputs. -/
abbrev Perm5 := Equiv.Perm (Fin 5)

/-- A binary comparison decision tree on five elements:
`node i j lo hi` compares the elements at positions `i` and `j`, continuing in
`lo` if the `i`-th is smaller and in `hi` otherwise; `leaf o` outputs `o`. -/
inductive CompTree where
  | leaf : Perm5 → CompTree
  | node : Fin 5 → Fin 5 → CompTree → CompTree → CompTree
  deriving Inhabited

namespace CompTree

/-- The depth of a comparison tree: the worst-case number of comparisons. -/
def depth : CompTree → ℕ
  | .leaf _ => 0
  | .node _ _ l r => max l.depth r.depth + 1

/-- Running the tree on the input whose ranking is `σ`. -/
def run : CompTree → Perm5 → Perm5
  | .leaf o, _ => o
  | .node i j l r, σ => if σ i < σ j then l.run σ else r.run σ

/-- The finite set of permutations appearing at the leaves of a tree. -/
def outputs : CompTree → Finset Perm5
  | .leaf o => {o}
  | .node _ _ l r => l.outputs ∪ r.outputs

/-- Every result of a run is a leaf label. -/
theorem run_mem_outputs (t : CompTree) (σ : Perm5) : t.run σ ∈ t.outputs := by
  induction t with
  | leaf o => simp [run, outputs]
  | node i j l r ihl ihr =>
      by_cases h : σ i < σ j <;> simp [run, outputs, h, ihl, ihr]

/-- A tree of depth `d` has at most `2 ^ d` distinct leaf labels. -/
theorem card_outputs_le (t : CompTree) : t.outputs.card ≤ 2 ^ t.depth := by
  induction t with
  | leaf o => simp [outputs, depth]
  | node i j l r ihl ihr =>
      refine (Finset.card_union_le _ _).trans ?_
      have hl : l.outputs.card ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : r.outputs.card ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc l.outputs.card + r.outputs.card
          ≤ 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) := by omega
        _ = 2 ^ (max l.depth r.depth + 1) := by ring

/-! ### The model is not vacuous: correct comparison trees exist -/

/-- The comparison tree that asks the comparisons listed in `ps` one after another,
keeping track of the set `S` of rankings still consistent with the answers, and
finally outputs some remaining consistent ranking. -/
noncomputable def build : List (Fin 5 × Fin 5) → Finset Perm5 → CompTree
  | [], S => .leaf S.toList.headI
  | (i, j) :: ps, S =>
      .node i j (build ps (S.filter (fun τ => τ i < τ j)))
                (build ps (S.filter (fun τ => τ j ≤ τ i)))

/-- Running `build ps S` on an input from `S` returns an element of `S` that answers
all the comparisons in `ps` exactly as the input does. -/
theorem run_build (ps : List (Fin 5 × Fin 5)) (S : Finset Perm5) (σ : Perm5) (hσ : σ ∈ S) :
    (build ps S).run σ ∈ S ∧
      ∀ p ∈ ps, (((build ps S).run σ) p.1 < ((build ps S).run σ) p.2 ↔ σ p.1 < σ p.2) := by
  induction ps generalizing S with
  | nil =>
      refine ⟨?_, by simp⟩
      have hne : S.toList ≠ [] := by
        intro hnil
        have : σ ∈ S.toList := by simpa using hσ
        simp [hnil] at this
      have hmem : S.toList.headI ∈ S.toList := by
        cases hl : S.toList with
        | nil => exact absurd hl hne
        | cons a t => simp
      simpa [build, run] using hmem
  | cons p ps ih =>
      obtain ⟨i, j⟩ := p
      by_cases h : σ i < σ j
      · have hmem : σ ∈ S.filter (fun τ => τ i < τ j) := Finset.mem_filter.mpr ⟨hσ, h⟩
        obtain ⟨h1, h2⟩ := ih _ hmem
        simp only [build, run, if_pos h]
        rw [Finset.mem_filter] at h1
        refine ⟨h1.1, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨fun _ => h, fun _ => h1.2⟩
        · exact h2 q hq
      · have h' : σ j ≤ σ i := not_lt.mp h
        have hmem : σ ∈ S.filter (fun τ => τ j ≤ τ i) := Finset.mem_filter.mpr ⟨hσ, h'⟩
        obtain ⟨h1, h2⟩ := ih _ hmem
        simp only [build, run, if_neg h]
        rw [Finset.mem_filter] at h1
        refine ⟨h1.1, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨fun hh => absurd hh (not_lt.mpr h1.2), fun hh => absurd hh h⟩
        · exact h2 q hq

/-- All ordered pairs of positions. -/
def allPairs : List (Fin 5 × Fin 5) :=
  (List.finRange 5).flatMap (fun i => (List.finRange 5).map (fun j => (i, j)))

theorem mem_allPairs (i j : Fin 5) : (i, j) ∈ allPairs := by
  simp [allPairs, List.mem_flatMap]

end CompTree

/-- A ranking of the five elements is determined by all its pairwise comparisons. -/
theorem eq_of_comparisons {σ τ : Perm5} (h : ∀ i j, (τ i < τ j ↔ σ i < σ j)) : τ = σ := by
  have hg : StrictMono (fun a => τ (σ.symm a)) := by
    intro a b hab
    simp only
    rw [h]
    simpa using hab
  have hgs : StrictMono (fun a => σ (τ.symm a)) := by
    intro a b hab
    by_contra hc
    push_neg at hc
    rcases lt_or_eq_of_le hc with hlt | heq
    · have := (h (τ.symm b) (τ.symm a)).mpr hlt
      simp at this
      omega
    · have h1 : τ.symm b = τ.symm a := by simpa using congrArg σ.symm heq
      have : b = a := by simpa using congrArg τ h1
      omega
  ext i
  have h1 : σ i ≤ τ i := by simpa using hg.le_apply (x := σ i)
  have h2 : τ i ≤ σ i := by simpa using hgs.le_apply (x := τ i)
  omega

/-- There **is** a correct comparison tree for five elements, so the hypothesis of the
lower bound below is satisfiable and the statement is not vacuous. -/
theorem exists_correct_tree : ∃ t : CompTree, ∀ σ : Perm5, t.run σ = σ := by
  refine ⟨CompTree.build CompTree.allPairs Finset.univ, fun σ => ?_⟩
  obtain ⟨-, h⟩ := CompTree.run_build CompTree.allPairs Finset.univ σ (Finset.mem_univ σ)
  exact eq_of_comparisons (fun i j => h (i, j) (CompTree.mem_allPairs i j))

/-- There are `5! = 120` possible rankings of five elements. -/
theorem card_perm5 : Fintype.card Perm5 = Nat.factorial 5 := by
  simp [Fintype.card_perm]

/-- A correct comparison tree must have at least `5!` leaf labels. -/
theorem factorial_le_card_outputs (t : CompTree) (hcorrect : ∀ σ : Perm5, t.run σ = σ) :
    Nat.factorial 5 ≤ t.outputs.card := by
  have huniv : (Finset.univ : Finset Perm5) ⊆ t.outputs := by
    intro σ _
    have := t.run_mem_outputs σ
    rwa [hcorrect σ] at this
  calc Nat.factorial 5 = (Finset.univ : Finset Perm5).card := by
        rw [Finset.card_univ, card_perm5]
    _ ≤ t.outputs.card := Finset.card_le_card huniv

/-- **Comparison-sort lower bound for 5 elements.**
Any correct comparison decision tree sorting five elements needs, in the worst
case, at least `⌈log₂ (5!)⌉ = 7` comparisons. -/
theorem sorting_lb_5 (t : CompTree) (hcorrect : ∀ σ : Perm5, t.run σ = σ) :
    Nat.clog 2 (Nat.factorial 5) ≤ t.depth := by
  have h : Nat.factorial 5 ≤ 2 ^ t.depth :=
    (factorial_le_card_outputs t hcorrect).trans t.card_outputs_le
  exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr h

/-- The bound is the expected numeral: `⌈log₂ 120⌉ = 7`. -/
theorem clog_factorial_five : Nat.clog 2 (Nat.factorial 5) = 7 := by
  norm_num [Nat.factorial]

/-- Restatement of the lower bound with the explicit constant `7`. -/
theorem sorting_lb_5' (t : CompTree) (hcorrect : ∀ σ : Perm5, t.run σ = σ) :
    7 ≤ t.depth := by
  have := sorting_lb_5 t hcorrect
  rwa [clog_factorial_five] at this

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

