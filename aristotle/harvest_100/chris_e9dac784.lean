/-
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree sorting three elements.
An internal node compares the (unknown) input values at two positions `i j : Fin 3`,
and branches on the outcome; a leaf outputs a permutation. -/
inductive CompTree : Type
  | leaf : Equiv.Perm (Fin 3) → CompTree
  | node : Fin 3 → Fin 3 → CompTree → CompTree → CompTree
  deriving Inhabited

namespace CompTree

/-- The worst-case number of comparisons performed by the tree. -/
def depth : CompTree → ℕ
  | leaf _ => 0
  | node _ _ l r => 1 + max (depth l) (depth r)

/-- Running the tree on an input.  An input is encoded by a permutation `σ` of `Fin 3`,
where `σ k` is the rank of the element in position `k`; the comparison of positions
`i` and `j` therefore returns whether `σ i < σ j`. -/
def run : CompTree → Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3)
  | leaf p, _ => p
  | node i j l r, σ => if σ i < σ j then run l σ else run r σ

/-- A tree of depth `d` can distinguish at most `2 ^ d` inputs: any set of inputs on
which the tree answers correctly (i.e. outputs the input's own ranking) has at most
`2 ^ depth` elements. -/
theorem card_le_two_pow_depth (t : CompTree) (S : Finset (Equiv.Perm (Fin 3)))
    (hS : ∀ σ ∈ S, t.run σ = σ) : S.card ≤ 2 ^ t.depth := by
  induction t generalizing S with
  | leaf p =>
      have : S ⊆ {p} := by
        intro σ hσ
        have := hS σ hσ
        simp [run] at this
        simp [← this]
      calc S.card ≤ ({p} : Finset (Equiv.Perm (Fin 3))).card := Finset.card_le_card this
        _ = 1 := by simp
        _ = 2 ^ (leaf p).depth := by simp [depth]
  | node i j l r ihl ihr =>
      classical
      set P : Equiv.Perm (Fin 3) → Prop := fun σ => σ i < σ j with hP
      have hsplit : (S.filter P).card + (S.filter (fun σ => ¬ P σ)).card = S.card :=
        Finset.card_filter_add_card_filter_not (p := P)
      have hl : (S.filter P).card ≤ 2 ^ l.depth := by
        refine ihl _ ?_
        intro σ hσ
        rw [Finset.mem_filter] at hσ
        have h1 := hS σ hσ.1
        rw [run, if_pos hσ.2] at h1
        exact h1
      have hr : (S.filter (fun σ => ¬ P σ)).card ≤ 2 ^ r.depth := by
        refine ihr _ ?_
        intro σ hσ
        rw [Finset.mem_filter] at hσ
        have h1 := hS σ hσ.1
        rw [run, if_neg hσ.2] at h1
        exact h1
      have hml : (2:ℕ) ^ l.depth ≤ 2 ^ max l.depth r.depth :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hmr : (2:ℕ) ^ r.depth ≤ 2 ^ max l.depth r.depth :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have key : (2:ℕ) ^ (1 + max l.depth r.depth)
          = 2 ^ max l.depth r.depth + 2 ^ max l.depth r.depth := by
        rw [pow_add]; ring
      simp only [depth]
      rw [key]
      omega

end CompTree

/-- `⌈log₂ 3!⌉ = 3`. -/
theorem ceil_logb_factorial_three : ⌈Real.logb 2 (Nat.factorial 3)⌉₊ = 3 := by
  have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6]
  have hub : Real.logb 2 6 ≤ 3 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
    rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hlb : (2:ℝ) < Real.logb 2 6 := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [Nat.ceil_eq_iff (by norm_num)]
  constructor
  · push_cast; linarith
  · push_cast; linarith

/-- **Sorting lower bound for 3 elements.**  Any comparison-based sorting algorithm
for `3` elements — modelled as a decision tree that correctly outputs the ranking of
every one of the `3! = 6` possible inputs — performs at least `⌈log₂ 3!⌉ = 3`
comparisons in the worst case. -/
theorem sorting_lb_3 (t : CompTree) (hcorrect : ∀ σ : Equiv.Perm (Fin 3), t.run σ = σ) :
    ⌈Real.logb 2 (Nat.factorial 3)⌉₊ ≤ t.depth := by
  rw [ceil_logb_factorial_three]
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin 3))).card ≤ 2 ^ t.depth :=
    CompTree.card_le_two_pow_depth t _ (fun σ _ => hcorrect σ)
  have h6 : (Finset.univ : Finset (Equiv.Perm (Fin 3))).card = 6 := by
    simp [Finset.card_univ, Fintype.card_perm]
    decide
  rw [h6] at hcard
  by_contra h
  push_neg at h
  interval_cases hd : t.depth <;> simp_all

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

