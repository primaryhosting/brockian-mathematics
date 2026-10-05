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
def depth : CompTree → ℕ
  | leaf => 0
  | node _ _ l r => 1 + max (depth l) (depth r)

/-- The sequence of comparison outcomes ("the trace") produced when the algorithm `t` is
run on the input ordered according to the permutation `p`: the input at position `i` is
deemed smaller than the input at position `j` exactly when `p i < p j`. -/
def run : CompTree → Equiv.Perm (Fin 4) → List Bool
  | leaf, _ => []
  | node i j l r, p => if p i < p j then true :: run l p else false :: run r p

end CompTree

open CompTree

/-- Key counting lemma: if the algorithm `t` produces pairwise distinct traces on a finite
set `S` of input orderings, then `S` has at most `2 ^ depth t` elements. -/
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
theorem clog_two_factorial_four : Nat.clog 2 (Nat.factorial 4) = 5 := by
  norm_num [Nat.factorial]

/-- **Comparison-sort lower bound for 4 elements.**

Let `t` be any comparison-based sorting algorithm for 4 elements, presented as a decision
tree whose internal nodes compare two input positions.  Assume it is correct, in the sense
that there is a function `out` reading off the sorted order from the sequence of
comparison outcomes, with `out (run t p) = p` for every input ordering `p`.
Then `t` performs at least `⌈log₂ (4!)⌉ = 5` comparisons in the worst case. -/
theorem sorting_lb_4 (t : CompTree) (out : List Bool → Equiv.Perm (Fin 4))
    (hout : ∀ p : Equiv.Perm (Fin 4), out (run t p) = p) :
    Nat.clog 2 (Nat.factorial 4) ≤ depth t := by
  classical
  have hinj : ∀ p ∈ (Finset.univ : Finset (Equiv.Perm (Fin 4))),
      ∀ q ∈ (Finset.univ : Finset (Equiv.Perm (Fin 4))), run t p = run t q → p = q := by
    intro p _ q _ h
    rw [← hout p, ← hout q, h]
  have hcard := card_le_two_pow_depth t Finset.univ hinj
  have h24 : (Finset.univ : Finset (Equiv.Perm (Fin 4))).card = 24 := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    decide
  rw [h24] at hcard
  rw [clog_two_factorial_four]
  by_contra hlt
  push_neg at hlt
  have hd : depth t ≤ 4 := by omega
  have : (2 : ℕ) ^ depth t ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hd
  omega

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

