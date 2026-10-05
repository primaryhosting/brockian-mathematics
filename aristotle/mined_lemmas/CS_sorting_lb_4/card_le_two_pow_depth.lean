import Mathlib

/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- A comparison-based sorting algorithm for 4 elements, modelled as a binary decision
tree.  A `node i j l r` compares the inputs at positions `i` and `j`; the algorithm then
continues in the subtree `l` (if the comparison succeeded) or `r` (if it failed).
A `leaf` is a point where the algorithm stops making comparisons and outputs an answer. -/
inductive CompTree : Type
  | leaf : CompTree
  | node : Fin 4 → Fin 4 → CompTree → CompTree → CompTree
  deriving Inhabited

namespace CompTree

/-- The worst-case number of comparisons performed by the algorithm, i.e. the depth of
the decision tree. -/

theorem card_le_two_pow_depth :
    ∀ (t : CompTree) (S : Finset (Equiv.Perm (Fin 4))),
      (∀ p ∈ S, ∀ q ∈ S, run t p = run t q → p = q) → S.card ≤ 2 ^ depth t := by
  intro t
  induction t with
  | leaf =>
      intro S hS
      have : S.card ≤ 1 := by
        refine Finset.card_le_one.mpr ?_
        intro p hp q hq
        exact hS p hp q hq rfl
      simpa [depth] using this
  | node i j l r ihl ihr =>
      intro S hS
      classical
      set S0 : Finset (Equiv.Perm (Fin 4)) := S.filter (fun p => p i < p j)
      set S1 : Finset (Equiv.Perm (Fin 4)) := S.filter (fun p => ¬ (p i < p j))
      have hsplit : S0.card + S1.card = S.card :=
        Finset.card_filter_add_card_filter_not (s := S)
          (p := fun p : Equiv.Perm (Fin 4) => p i < p j)
      have h0 : S0.card ≤ 2 ^ depth l := by
        refine ihl S0 ?_
        intro p hp q hq hpq
        have hp' := (Finset.mem_filter.mp hp)
        have hq' := (Finset.mem_filter.mp hq)
        refine hS p hp'.1 q hq'.1 ?_
        simp [run, hp'.2, hq'.2, hpq]
      have h1 : S1.card ≤ 2 ^ depth r := by
        refine ihr S1 ?_
        intro p hp q hq hpq
        have hp' := (Finset.mem_filter.mp hp)
        have hq' := (Finset.mem_filter.mp hq)
        refine hS p hp'.1 q hq'.1 ?_
        simp [run, hp'.2, hq'.2, hpq]
      have hl : (2 : ℕ) ^ depth l ≤ 2 ^ max (depth l) (depth r) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hr : (2 : ℕ) ^ depth r ≤ 2 ^ max (depth l) (depth r) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have : S.card ≤ 2 ^ max (depth l) (depth r) + 2 ^ max (depth l) (depth r) := by
        rw [← hsplit]
        exact Nat.add_le_add (h0.trans hl) (h1.trans hr)
      have hpow : (2 : ℕ) ^ depth (node i j l r)
          = 2 ^ max (depth l) (depth r) + 2 ^ max (depth l) (depth r) := by
        simp only [depth, pow_add, pow_one, two_mul]
      rw [hpow]
      exact this

/-- `⌈log₂ (4!)⌉ = 5`. -/
