import Mathlib

/-!
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
Note: Lean 4 requires `import` to be the first command of a file, so the header
comment above appears immediately after the imports of this file.
-/

namespace CS

/-- A (binary) decision tree over inputs `I` producing outputs `O`.  An internal node
carries an arbitrary boolean query on the input; in a comparison sort the query is a
single comparison `a i < a j`, so this model is *more* general than comparison sorts
and the lower bound proved below applies a fortiori to them. -/
inductive DecisionTree (I O : Type) : Type
  | leaf : O → DecisionTree I O
  | node : (I → Bool) → DecisionTree I O → DecisionTree I O → DecisionTree I O

namespace DecisionTree

variable {I O : Type}

/-- The output produced by running the decision tree on a given input. -/

theorem card_image_run_le [DecidableEq O] (t : DecisionTree I O) (s : Finset I) :
    (s.image t.run).card ≤ 2 ^ t.depth := by
  induction t generalizing s with
  | leaf o =>
      have hsub : s.image (run (leaf o : DecisionTree I O)) ⊆ {o} := by
        intro x hx
        simp only [Finset.mem_image] at hx
        obtain ⟨a, _, rfl⟩ := hx
        simp [run]
      calc (s.image (run (leaf o : DecisionTree I O))).card ≤ ({o} : Finset O).card :=
            Finset.card_le_card hsub
        _ = 1 := by simp
        _ ≤ 2 ^ (depth (leaf o : DecisionTree I O)) := by simp [depth]
  | node q l r ihl ihr =>
      have hsub : s.image (run (node q l r)) ⊆
          ((s.filter (fun i => q i)).image l.run) ∪ ((s.filter (fun i => ¬ q i)).image r.run) := by
        intro x hx
        simp only [Finset.mem_image] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        by_cases h : q a
        · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨a, by simp [ha, h], by simp [run, h]⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨a, by simp [ha, h], by simp [run, h]⟩)
      have h1 := ihl (s.filter (fun i => q i))
      have h2 := ihr (s.filter (fun i => ¬ q i))
      have hl : (2:ℕ) ^ l.depth ≤ 2 ^ (max l.depth r.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hr : (2:ℕ) ^ r.depth ≤ 2 ^ (max l.depth r.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      calc (s.image (run (node q l r))).card ≤ _ := Finset.card_le_card hsub
        _ ≤ ((s.filter (fun i => q i)).image l.run).card
              + ((s.filter (fun i => ¬ q i)).image r.run).card := Finset.card_union_le _ _
        _ ≤ 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) :=
              Nat.add_le_add (h1.trans hl) (h2.trans hr)
        _ = 2 ^ (depth (node q l r)) := by rw [depth, pow_succ]; ring

end DecisionTree

/-- **Sorting lower bound for 3 elements.**  Any comparison sort of `3` elements —
modelled as a decision tree whose internal nodes ask arbitrary yes/no questions about
the input ordering, and which must output the correct sorting permutation for each of
the `3! = 6` possible input orders — performs at least `⌈log₂ (3!)⌉ = 3` comparisons in
the worst case.  (Since arbitrary boolean queries are allowed, this is stronger than the
statement restricted to comparison queries.) -/
