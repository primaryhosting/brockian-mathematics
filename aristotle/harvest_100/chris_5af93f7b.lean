/-
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- A comparison-based decision tree sorting 5 elements: an internal node
`node i j l r` compares the keys at positions `i` and `j`, descending into `l`
when `a i ≤ a j` and into `r` otherwise; a leaf outputs a permutation of the
positions. -/
inductive CompTree where
  | leaf : Equiv.Perm (Fin 5) → CompTree
  | node : Fin 5 → Fin 5 → CompTree → CompTree → CompTree
  deriving Inhabited

namespace CompTree

/-- The worst-case number of comparisons performed by the decision tree. -/
def depth : CompTree → ℕ
  | .leaf _ => 0
  | .node _ _ l r => max (depth l) (depth r) + 1

/-- Running the decision tree on the input keys `a` yields the permutation
stored at the leaf that the comparisons lead to. -/
def run (a : Fin 5 → ℕ) : CompTree → Equiv.Perm (Fin 5)
  | .leaf σ => σ
  | .node i j l r => if a i ≤ a j then run a l else run a r

/-- The finite set of permutations occurring at the leaves of the tree. -/
def outputs : CompTree → Finset (Equiv.Perm (Fin 5))
  | .leaf σ => {σ}
  | .node _ _ l r => outputs l ∪ outputs r

/-- The tree is a correct comparison sort: on any input with distinct keys the
permutation it returns arranges the keys in increasing order. -/
def Sorts (t : CompTree) : Prop :=
  ∀ a : Fin 5 → ℕ, Function.Injective a → Monotone (a ∘ (run a t))

lemma run_mem_outputs (a : Fin 5 → ℕ) (t : CompTree) : run a t ∈ outputs t := by
  induction t with
  | leaf σ => simp [run, outputs]
  | node i j l r ihl ihr =>
      by_cases h : a i ≤ a j <;> simp [run, outputs, h, ihl, ihr]

lemma card_outputs_le (t : CompTree) : (outputs t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf σ => simp [outputs, depth]
  | node i j l r ihl ihr =>
      refine le_trans (Finset.card_union_le _ _) ?_
      have hl : (outputs l).card ≤ 2 ^ max (depth l) (depth r) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : (outputs r).card ≤ 2 ^ max (depth l) (depth r) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc (outputs l).card + (outputs r).card
          ≤ 2 ^ max (depth l) (depth r) + 2 ^ max (depth l) (depth r) := by omega
        _ = 2 ^ depth (.node i j l r) := by simp [depth, pow_succ]; ring

/-- On the input whose key at position `i` is `p i`, a correct sorting tree must
return `p⁻¹`. -/
lemma run_eq_inv (t : CompTree) (h : Sorts t) (p : Equiv.Perm (Fin 5)) :
    run (fun i => ((p i : Fin 5) : ℕ)) t = p⁻¹ := by
  have hainj : Function.Injective (fun i => ((p i : Fin 5) : ℕ)) := by
    intro x y hxy
    exact p.injective (Fin.val_injective hxy)
  have hmono := h _ hainj
  obtain ⟨σ, hσ⟩ : ∃ σ, run (fun i => ((p i : Fin 5) : ℕ)) t = σ := ⟨_, rfl⟩
  rw [hσ] at hmono ⊢
  have hmono' : Monotone ⇑(p * σ) := by
    intro x y hxy
    have hxy' := hmono hxy
    simp only [Function.comp_apply] at hxy'
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Fin.le_def]
    exact hxy'
  have hpσ : p * σ = 1 := (Equiv.Perm.monotone_iff _).mp hmono'
  exact (inv_eq_of_mul_eq_one_right hpσ).symm

end CompTree

/-- **Comparison-sort lower bound for 5 elements.** Any correct comparison-based
sorting decision tree on 5 elements has worst-case depth (number of
comparisons) at least `⌈log₂(5!)⌉ = 7`. -/
theorem sorting_lb_5 (t : CompTree) (h : CompTree.Sorts t) :
    Nat.clog 2 (Nat.factorial 5) ≤ CompTree.depth t := by
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin 5))).card ≤ (CompTree.outputs t).card := by
    refine Finset.card_le_card_of_injOn (fun p => p⁻¹) ?_ ?_
    · intro p _
      have : p⁻¹ ∈ CompTree.outputs t := by
        rw [← CompTree.run_eq_inv t h p]
        exact CompTree.run_mem_outputs _ t
      simpa using this
    · intro x _ y _ hxy
      simpa using congrArg (fun z : Equiv.Perm (Fin 5) => z⁻¹) hxy
  have h120 : (Finset.univ : Finset (Equiv.Perm (Fin 5))).card = 120 := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    decide
  have hfac : Nat.factorial 5 = 120 := by decide
  have : (120 : ℕ) ≤ 2 ^ CompTree.depth t := by
    calc (120 : ℕ) = (Finset.univ : Finset (Equiv.Perm (Fin 5))).card := h120.symm
      _ ≤ (CompTree.outputs t).card := hcard
      _ ≤ 2 ^ CompTree.depth t := CompTree.card_outputs_le t
  rw [hfac]
  exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr this

/-- The bound made explicit: `⌈log₂(5!)⌉ = 7`, so any correct comparison sort of
5 elements performs at least 7 comparisons in the worst case. -/
theorem sorting_lb_5_seven (t : CompTree) (h : CompTree.Sorts t) :
    7 ≤ CompTree.depth t := by
  have hclog : Nat.clog 2 (Nat.factorial 5) = 7 := by
    norm_num [Nat.factorial]
  exact hclog ▸ sorting_lb_5 t h

/-! ### Non-vacuity: a correct comparison sorting tree exists -/

namespace CompTree

/-- Update a two-argument Boolean function at one pair. -/
def upd (f : Fin 5 → Fin 5 → Bool) (i j : Fin 5) (b : Bool) : Fin 5 → Fin 5 → Bool :=
  fun x y => if x = i ∧ y = j then b else f x y

/-- The rank of `i` according to the recorded comparison answers `f`, i.e. the
number of positions `j ≠ i` whose key is recorded as `≤` the key at `i`. -/
def rankOf (f : Fin 5 → Fin 5 → Bool) (i : Fin 5) : Fin 5 :=
  ⟨(Finset.univ.filter (fun j => j ≠ i ∧ f j i = true)).card, by
    have hsub : (Finset.univ.filter (fun j => j ≠ i ∧ f j i = true)) ⊆
        (Finset.univ.erase i) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact Finset.mem_erase.mpr ⟨hj.1, Finset.mem_univ j⟩
    have := Finset.card_le_card hsub
    have h4 : (Finset.univ.erase i).card = 4 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp
    omega⟩

/-- The permutation output at a leaf: the inverse of the rank function, when the
recorded answers make the rank function a bijection. -/
noncomputable def permOfRank (f : Fin 5 → Fin 5 → Bool) : Equiv.Perm (Fin 5) :=
  if h : Function.Bijective (rankOf f) then (Equiv.ofBijective _ h).symm else 1

/-- The decision tree that queries every pair in the list `L` in turn and then
outputs the permutation determined by the recorded answers. -/
noncomputable def build : List (Fin 5 × Fin 5) → (Fin 5 → Fin 5 → Bool) → CompTree
  | [], f => .leaf (permOfRank f)
  | (i, j) :: rest, f =>
      .node i j (build rest (upd f i j true)) (build rest (upd f i j false))

lemma run_build (a : Fin 5 → ℕ) :
    ∀ (L : List (Fin 5 × Fin 5)) (f : Fin 5 → Fin 5 → Bool),
      run a (build L f) =
        permOfRank (fun x y => if (x, y) ∈ L then decide (a x ≤ a y) else f x y) := by
  intro L
  induction L with
  | nil => intro f; simp [build, run]
  | cons ij rest ih =>
      obtain ⟨i, j⟩ := ij
      intro f
      by_cases hij : a i ≤ a j
      · have : run a (build ((i, j) :: rest) f) = run a (build rest (upd f i j true)) := by
          simp [build, run, hij]
        rw [this, ih]
        congr 1
        funext x y
        by_cases hr : (x, y) ∈ rest
        · simp [hr]
        · by_cases he : x = i ∧ y = j
          · simp [upd, he, hij]
          · simp [hr, upd, List.mem_cons, Prod.ext_iff, he]
      · have : run a (build ((i, j) :: rest) f) = run a (build rest (upd f i j false)) := by
          simp [build, run, hij]
        rw [this, ih]
        congr 1
        funext x y
        by_cases hr : (x, y) ∈ rest
        · simp [hr]
        · by_cases he : x = i ∧ y = j
          · simp [upd, he, hij]
          · simp [hr, upd, List.mem_cons, Prod.ext_iff, he]

/-- A comparison tree querying all ordered pairs of positions. -/
noncomputable def sortTree : CompTree :=
  build (Finset.univ : Finset (Fin 5 × Fin 5)).toList (fun _ _ => true)

lemma run_sortTree (a : Fin 5 → ℕ) :
    run a sortTree = permOfRank (fun x y => decide (a x ≤ a y)) := by
  rw [sortTree, run_build]
  congr 1
  funext x y
  have : (x, y) ∈ (Finset.univ : Finset (Fin 5 × Fin 5)).toList := by
    simp
  simp [this]

lemma rankOf_val (a : Fin 5 → ℕ) (i : Fin 5) :
    ((rankOf (fun x y => decide (a x ≤ a y)) i : Fin 5) : ℕ) =
      (Finset.univ.filter (fun j => j ≠ i ∧ a j ≤ a i)).card := by
  simp [rankOf]

lemma rankOf_strictMono (a : Fin 5 → ℕ) {i j : Fin 5}
    (hlt : a i < a j) :
    rankOf (fun x y => decide (a x ≤ a y)) i < rankOf (fun x y => decide (a x ≤ a y)) j := by
  rw [Fin.lt_def, rankOf_val, rankOf_val]
  apply Finset.card_lt_card
  constructor
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    refine ⟨?_, le_of_lt (lt_of_le_of_lt hk.2 hlt)⟩
    intro hkj
    exact absurd (hkj ▸ hk.2) (not_le.mpr hlt)
  · intro hsub
    have hi : i ∈ Finset.univ.filter (fun k => k ≠ j ∧ a k ≤ a j) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => absurd (h ▸ hlt) (lt_irrefl _), le_of_lt hlt⟩
    have := hsub hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.1 rfl

lemma rankOf_bijective (a : Fin 5 → ℕ) (hinj : Function.Injective a) :
    Function.Bijective (rankOf (fun x y => decide (a x ≤ a y))) := by
  rw [← Finite.injective_iff_bijective]
  intro x y hxy
  rcases lt_trichotomy (a x) (a y) with h | h | h
  · exact absurd hxy (ne_of_lt (rankOf_strictMono a h))
  · exact hinj h
  · exact absurd hxy.symm (ne_of_lt (rankOf_strictMono a h))

/-- `sortTree` is a correct comparison sort. -/
lemma sorts_sortTree : Sorts sortTree := by
  intro a hinj
  rw [run_sortTree]
  have hb := rankOf_bijective a hinj
  rw [permOfRank, dif_pos hb]
  intro x y hxy
  simp only [Function.comp_apply]
  by_contra hcon
  have hlt : a ((Equiv.ofBijective _ hb).symm y) < a ((Equiv.ofBijective _ hb).symm x) :=
    lt_of_not_ge hcon
  have hstep := rankOf_strictMono a hlt
  rw [Equiv.ofBijective_apply_symm_apply _ hb y, Equiv.ofBijective_apply_symm_apply _ hb x]
    at hstep
  exact absurd hxy (not_le.mpr hstep)

end CompTree

/-- The lower bound is not vacuous: correct comparison sorting trees for 5
elements do exist. -/
theorem exists_sorting_tree : ∃ t : CompTree, CompTree.Sorts t :=
  ⟨CompTree.sortTree, CompTree.sorts_sortTree⟩

end CS

