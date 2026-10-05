import Mathlib
/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-- A comparison-based decision tree sorting 4 elements.

An input is modelled by a permutation `σ : Equiv.Perm (Fin 4)`, where `σ i` is the rank
of the `i`-th input element (so all inputs are distinct and every ranking occurs).
An internal node `node i j l r` performs the single comparison `σ i ≤ σ j`, i.e. it asks
whether the `i`-th element is smaller than the `j`-th element, and branches accordingly.
A leaf outputs a permutation, the algorithm's claimed ranking of the input. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 4) → DTree
  | node : Fin 4 → Fin 4 → DTree → DTree → DTree

/-- The output of the decision tree on the input with ranking `σ`. -/
def run : DTree → Equiv.Perm (Fin 4) → Equiv.Perm (Fin 4)
  | DTree.leaf p, _ => p
  | DTree.node i j l r, σ => if σ i ≤ σ j then run l σ else run r σ

/-- The worst-case number of comparisons performed by the decision tree. -/
def depth : DTree → ℕ
  | DTree.leaf _ => 0
  | DTree.node _ _ l r => 1 + max (depth l) (depth r)

/-- A decision tree sorts correctly if on every input it outputs the correct ranking. -/
def Correct (t : DTree) : Prop := ∀ σ : Equiv.Perm (Fin 4), run t σ = σ

/-- The set of possible outputs of a decision tree has at most `2 ^ depth` elements. -/
theorem card_outputs_le (t : DTree) :
    (Finset.univ.image (run t)).card ≤ 2 ^ depth t := by
  induction t with
  | leaf p =>
      simp only [run, depth, pow_zero]
      rw [Finset.image_const Finset.univ_nonempty]
      simp
  | node i j l r ihl ihr =>
      have hsub : Finset.univ.image (run (DTree.node i j l r)) ⊆
          Finset.univ.image (run l) ∪ Finset.univ.image (run r) := by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨σ, hσ⟩ := hx
        by_cases h : σ i ≤ σ j
        · refine Finset.mem_union_left _ ?_
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨σ, by rw [← hσ]; simp [run, h]⟩
        · refine Finset.mem_union_right _ ?_
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨σ, by rw [← hσ]; simp [run, h]⟩
      calc (Finset.univ.image (run (DTree.node i j l r))).card
          ≤ (Finset.univ.image (run l) ∪ Finset.univ.image (run r)).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.univ.image (run l)).card + (Finset.univ.image (run r)).card :=
            Finset.card_union_le _ _
        _ ≤ 2 ^ depth l + 2 ^ depth r := Nat.add_le_add ihl ihr
        _ ≤ 2 ^ max (depth l) (depth r) + 2 ^ max (depth l) (depth r) :=
            Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
              (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
        _ = 2 ^ depth (DTree.node i j l r) := by
            rw [depth, pow_add]
            ring

/-- A correct comparison sort of 4 elements must have at least `4! = 24` distinct outputs,
hence `2 ^ depth ≥ 24`. -/
theorem factorial_le_two_pow_depth (t : DTree) (h : Correct t) :
    Nat.factorial 4 ≤ 2 ^ depth t := by
  have himg : Finset.univ.image (run t) = (Finset.univ : Finset (Equiv.Perm (Fin 4))) := by
    apply Finset.eq_univ_of_forall
    intro σ
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨σ, h σ⟩
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin 4))).card = Nat.factorial 4 := by
    simp [Fintype.card_perm]
  have := card_outputs_le t
  rw [himg, hcard] at this
  exact this

/-- Any correct comparison sort of 4 elements performs at least 5 comparisons
in the worst case. -/
theorem five_le_depth (t : DTree) (h : Correct t) : 5 ≤ depth t := by
  by_contra hlt
  push_neg at hlt
  have h24 : Nat.factorial 4 ≤ 2 ^ depth t := factorial_le_two_pow_depth t h
  have : (2:ℕ) ^ depth t ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp [Nat.factorial] at h24
  omega

/-- **Comparison-sort lower bound for 4 elements.**
Any comparison-based sorting algorithm for 4 elements (modelled as a decision tree that
outputs the correct ranking on every input) requires at least `⌈log₂ (4!)⌉ = 5`
comparisons in the worst case. -/
theorem sorting_lb_4 (t : DTree) (h : Correct t) :
    ⌈Real.logb 2 (Nat.factorial 4 : ℝ)⌉ ≤ (depth t : ℤ) := by
  have h5 : (5:ℕ) ≤ depth t := five_le_depth t h
  have hceil : ⌈Real.logb 2 (Nat.factorial 4 : ℝ)⌉ ≤ (5 : ℤ) := by
    rw [Int.ceil_le]
    have h24 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [h24]
    have hle : Real.logb 2 24 ≤ Real.logb 2 32 := by
      apply Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
    have h32 : Real.logb 2 32 = 5 := by
      rw [show (32:ℝ) = 2 ^ (5:ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one] <;> norm_num
    push_cast
    linarith
  exact le_trans hceil (by exact_mod_cast h5)

/-! ### Non-vacuity: correct decision trees do exist -/

/-- A permutation of `Fin 4` is determined by the outcomes of all comparisons. -/
theorem perm_eq_of_le_iff (σ τ : Equiv.Perm (Fin 4))
    (h : ∀ i j : Fin 4, σ i ≤ σ j ↔ τ i ≤ τ j) : σ = τ := by
  have hf : ∀ a b : Fin 4, a ≤ b ↔ (τ (σ.symm a)) ≤ (τ (σ.symm b)) := by
    intro a b
    have := h (σ.symm a) (σ.symm b)
    simpa using this
  let f : Fin 4 ≃o Fin 4 := ⟨σ.symm.trans τ, by intro a b; simpa using (hf a b).symm⟩
  have hid : f = OrderIso.refl _ := Subsingleton.elim _ _
  have h2 : ∀ a, τ (σ.symm a) = a := by
    intro a
    have := congrArg (fun g => g a) hid
    simpa [f] using this
  ext i
  have h3 := h2 (σ i)
  simp only [Equiv.symm_apply_apply] at h3
  simp [h3]

/-- Build a decision tree which asks the comparisons in `pairs` in order and, at each leaf,
outputs the first candidate consistent with the answers received. -/
def build : List (Fin 4 × Fin 4) → List (Equiv.Perm (Fin 4)) → DTree
  | [], cands => DTree.leaf cands.headI
  | (i, j) :: rest, cands =>
      DTree.node i j
        (build rest (cands.filter (fun σ => decide (σ i ≤ σ j))))
        (build rest (cands.filter (fun σ => decide ¬ (σ i ≤ σ j))))

theorem build_correct :
    ∀ (pairs : List (Fin 4 × Fin 4)) (cands : List (Equiv.Perm (Fin 4)))
      (σ : Equiv.Perm (Fin 4)), σ ∈ cands →
      (∀ τ ∈ cands, (∀ p ∈ pairs, (σ p.1 ≤ σ p.2 ↔ τ p.1 ≤ τ p.2)) → τ = σ) →
      run (build pairs cands) σ = σ
  | [], cands, σ, hmem, huniq => by
      have hne : cands ≠ [] := by
        intro hnil
        rw [hnil] at hmem
        simp at hmem
      have hhead : cands.headI ∈ cands := by
        cases cands with
        | nil => exact absurd rfl hne
        | cons a l => simp
      simpa [run, build] using huniq _ hhead (by simp)
  | (i, j) :: rest, cands, σ, hmem, huniq => by
      by_cases hc : σ i ≤ σ j
      · have hmem' : σ ∈ cands.filter (fun σ => decide (σ i ≤ σ j)) := by
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hmem, hc⟩
        have huniq' : ∀ τ ∈ cands.filter (fun σ => decide (σ i ≤ σ j)),
            (∀ p ∈ rest, (σ p.1 ≤ σ p.2 ↔ τ p.1 ≤ τ p.2)) → τ = σ := by
          intro τ hτ hagree
          simp only [List.mem_filter, decide_eq_true_eq] at hτ
          refine huniq τ hτ.1 ?_
          intro p hp
          rcases List.mem_cons.mp hp with hp | hp
          · subst hp; simp [hc, hτ.2]
          · exact hagree p hp
        simp only [run, build, if_pos hc]
        exact build_correct rest _ σ hmem' huniq'
      · have hmem' : σ ∈ cands.filter (fun σ => decide ¬ (σ i ≤ σ j)) := by
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hmem, hc⟩
        have huniq' : ∀ τ ∈ cands.filter (fun σ => decide ¬ (σ i ≤ σ j)),
            (∀ p ∈ rest, (σ p.1 ≤ σ p.2 ↔ τ p.1 ≤ τ p.2)) → τ = σ := by
          intro τ hτ hagree
          simp only [List.mem_filter, decide_eq_true_eq] at hτ
          refine huniq τ hτ.1 ?_
          intro p hp
          rcases List.mem_cons.mp hp with hp | hp
          · subst hp; simp [hc, hτ.2]
          · exact hagree p hp
        simp only [run, build, if_neg hc]
        exact build_correct rest _ σ hmem' huniq'

/-- The list of all ordered pairs of indices. -/
def allPairs : List (Fin 4 × Fin 4) :=
  (List.finRange 4).flatMap (fun i => (List.finRange 4).map (fun j => (i, j)))

theorem mem_allPairs : ∀ i j : Fin 4, (i, j) ∈ allPairs := by decide

/-- There does exist a correct comparison sort of 4 elements, so the lower bound above is
not vacuous. -/
theorem exists_correct : ∃ t : DTree, Correct t := by
  classical
  refine ⟨build allPairs (Finset.univ.toList), ?_⟩
  intro σ
  refine build_correct allPairs _ σ (by simp) ?_
  intro τ _ hagree
  refine (perm_eq_of_le_iff σ τ ?_).symm
  intro i j
  exact hagree (i, j) (mem_allPairs i j)

end CS

