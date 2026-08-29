import Mathlib

/-!
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- A comparison-sorting algorithm on `5` elements, modelled as a (binary) decision tree.
A `leaf p` outputs the permutation `p`; a `node i j l r` compares the keys at positions `i`
and `j` and continues in `l` if `key i ≤ key j`, and in `r` otherwise.  This is the standard
decision-tree model: the algorithm's only access to the input is through comparisons. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 5) → DTree
  | node : Fin 5 → Fin 5 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by the algorithm, i.e. the depth of the
decision tree. -/
def depth : DTree → ℕ
  | leaf _ => 0
  | node _ _ l r => max (depth l) (depth r) + 1

/-- Running the algorithm on an input given by the key function `k : Fin 5 → ℕ`. -/
def run : DTree → (Fin 5 → ℕ) → Equiv.Perm (Fin 5)
  | leaf p, _ => p
  | node i j l r, k => if k i ≤ k j then run l k else run r k

/-- The finite set of outputs that appear at the leaves of the tree. -/
def results : DTree → Finset (Equiv.Perm (Fin 5))
  | leaf p => {p}
  | node _ _ l r => results l ∪ results r

theorem run_mem_results (t : DTree) (k : Fin 5 → ℕ) : t.run k ∈ t.results := by
  induction t with
  | leaf p => simp [run, results]
  | node i j l r ihl ihr =>
      by_cases h : k i ≤ k j <;> simp [run, results, h, ihl, ihr]

theorem card_results_le (t : DTree) : t.results.card ≤ 2 ^ t.depth := by
  induction t with
  | leaf p => simp [results, depth]
  | node i j l r ihl ihr =>
      have h := Finset.card_union_le l.results r.results
      have hl : l.results.card ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : r.results.card ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc (results (node i j l r)).card ≤ l.results.card + r.results.card := h
        _ ≤ 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) := Nat.add_le_add hl hr
        _ = 2 ^ (depth (node i j l r)) := by rw [depth]; ring

end DTree

/-- Correctness of a comparison sort: on the input whose keys are the ranks given by a
permutation `σ`, the algorithm must output `σ`.  (Only permutation-valued inputs are
required to be sorted correctly, which makes this hypothesis weak, hence the lower bound
below strong.) -/
def Correct (t : DTree) : Prop :=
  ∀ σ : Equiv.Perm (Fin 5), t.run (fun i => (σ i : ℕ)) = σ

/-- A correct comparison sort must be able to produce all `5! = 120` permutations. -/
theorem results_eq_univ {t : DTree} (h : Correct t) : t.results = Finset.univ := by
  refine Finset.eq_univ_of_forall (fun σ => ?_)
  have := t.run_mem_results (fun i => (σ i : ℕ))
  rwa [h σ] at this

/-- A correct comparison sort on `5` elements makes at least `7` comparisons in the worst
case, since `2 ^ 6 < 5!`. -/
theorem seven_le_depth {t : DTree} (h : Correct t) : 7 ≤ t.depth := by
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin 5))).card = 120 := by
    simp [Finset.card_univ, Fintype.card_perm, Nat.factorial]
  have h120 : (120 : ℕ) ≤ 2 ^ t.depth := by
    have := t.card_results_le
    rwa [results_eq_univ h, hcard] at this
  by_contra hlt
  push_neg at hlt
  have : (2 : ℕ) ^ t.depth ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem ceil_logb_factorial_five : (⌈Real.logb 2 (Nat.factorial 5)⌉ : ℤ) = 7 := by
  have hf : ((Nat.factorial 5 : ℕ) : ℝ) = 120 := by norm_num [Nat.factorial]
  have h64 : Real.logb 2 64 = 6 := by
    rw [show (64:ℝ) = 2 ^ (6:ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one] <;> norm_num
  have h128 : Real.logb 2 128 = 7 := by
    rw [show (128:ℝ) = 2 ^ (7:ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one] <;> norm_num
  have h1 : Real.logb 2 64 < Real.logb 2 120 :=
    Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 2 120 ≤ Real.logb 2 128 :=
    (Real.logb_le_logb (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [hf, Int.ceil_eq_iff]
  constructor <;> push_cast <;> linarith

/-- **Comparison-sorting lower bound for 5 elements.**
Any correct comparison sort of `5` elements needs at least `⌈log₂ (5!)⌉ = 7` comparisons
in the worst case (the worst-case number of comparisons being the depth of its decision
tree). -/
theorem sorting_lb_5 {t : DTree} (h : Correct t) :
    ⌈Real.logb 2 (Nat.factorial 5)⌉ ≤ (t.depth : ℤ) := by
  rw [ceil_logb_factorial_five]
  exact_mod_cast seven_le_depth h

/-! ### Non-vacuity: correct comparison sorts do exist

The hypothesis `Correct t` of `CS.sorting_lb_5` is satisfiable: we build (a very naive)
correct comparison sort, which branches on all `25` ordered pairs of positions and keeps
track of the set of permutations still consistent with the answers received so far. -/

/-- An arbitrary element of a finite set of permutations (the identity if it is empty). -/
noncomputable def pick (S : Finset (Equiv.Perm (Fin 5))) : Equiv.Perm (Fin 5) :=
  if h : S.Nonempty then h.choose else 1

theorem pick_singleton (τ : Equiv.Perm (Fin 5)) : pick {τ} = τ := by
  unfold pick
  split
  · rename_i h
    have := h.choose_spec
    simpa using this
  · rename_i h
    exact absurd ⟨τ, by simp⟩ h

/-- The decision tree that queries all the pairs in `L`, narrowing down the candidate set `S`
of permutations, and finally outputs a remaining candidate. -/
noncomputable def build : List (Fin 5 × Fin 5) → Finset (Equiv.Perm (Fin 5)) → DTree
  | [], S => DTree.leaf (pick S)
  | (i, j) :: L, S =>
      DTree.node i j (build L (S.filter (fun σ => σ i ≤ σ j)))
                     (build L (S.filter (fun σ => ¬ (σ i ≤ σ j))))

theorem run_build (L : List (Fin 5 × Fin 5)) (S : Finset (Equiv.Perm (Fin 5)))
    (τ : Equiv.Perm (Fin 5)) :
    (build L S).run (fun i => (τ i : ℕ))
      = pick (S.filter (fun σ => ∀ p ∈ L, (σ p.1 ≤ σ p.2 ↔ τ p.1 ≤ τ p.2))) := by
  induction L generalizing S with
  | nil => simp [build, DTree.run]
  | cons p L ih =>
      obtain ⟨i, j⟩ := p
      by_cases hc : τ i ≤ τ j
      · have hc' : ((τ i : ℕ) ≤ (τ j : ℕ)) := hc
        simp only [build, DTree.run, if_pos hc', ih, Finset.filter_filter]
        congr 1
        ext σ
        simp only [Finset.mem_filter, List.mem_cons]
        constructor
        · rintro ⟨hs, h1, h2⟩
          refine ⟨hs, ?_⟩
          rintro p (rfl | hp)
          · exact ⟨fun _ => hc, fun _ => h1⟩
          · exact h2 p hp
        · rintro ⟨hs, h⟩
          exact ⟨hs, (h (i, j) (Or.inl rfl)).mpr hc, fun p hp => h p (Or.inr hp)⟩
      · have hc' : ¬ ((τ i : ℕ) ≤ (τ j : ℕ)) := hc
        simp only [build, DTree.run, if_neg hc', ih, Finset.filter_filter]
        congr 1
        ext σ
        simp only [Finset.mem_filter, List.mem_cons]
        constructor
        · rintro ⟨hs, h1, h2⟩
          refine ⟨hs, ?_⟩
          rintro p (rfl | hp)
          · exact ⟨fun hx => absurd hx h1, fun hx => absurd hx hc⟩
          · exact h2 p hp
        · rintro ⟨hs, h⟩
          exact ⟨hs, fun hx => hc ((h (i, j) (Or.inl rfl)).mp hx), fun p hp => h p (Or.inr hp)⟩

/-- Two permutations of `Fin 5` inducing the same comparisons are equal. -/
theorem perm_eq_of_agree {σ τ : Equiv.Perm (Fin 5)} (h : ∀ a b, σ a ≤ σ b ↔ τ a ≤ τ b) :
    σ = τ := by
  have hmono : Monotone ⇑(τ * σ⁻¹) := by
    intro x y hxy
    simp only [Equiv.Perm.mul_apply]
    rw [← h]
    simpa using hxy
  have h1 := (Equiv.Perm.monotone_iff _).mp hmono
  have h2 : τ = σ := by
    have := congrArg (fun e => e * σ) h1
    simpa [mul_assoc] using this
  exact h2.symm

/-- The class of correct comparison sorts is nonempty, so `CS.sorting_lb_5` is not vacuous. -/
theorem exists_correct : ∃ t : DTree, Correct t := by
  refine ⟨build (Finset.univ : Finset (Fin 5 × Fin 5)).toList Finset.univ, fun τ => ?_⟩
  rw [run_build]
  have hset : (Finset.univ.filter
      (fun σ : Equiv.Perm (Fin 5) => ∀ p ∈ (Finset.univ : Finset (Fin 5 × Fin 5)).toList,
        (σ p.1 ≤ σ p.2 ↔ τ p.1 ≤ τ p.2))) = {τ} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Finset.mem_toList]
    constructor
    · intro hσ
      exact perm_eq_of_agree (fun a b => hσ (a, b) trivial)
    · rintro rfl
      intro p _
      rfl
  rw [hset, pick_singleton]

end CS

