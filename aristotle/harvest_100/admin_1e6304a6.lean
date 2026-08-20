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
def run : DecisionTree I O → I → O
  | leaf o, _ => o
  | node q l r, i => if q i then run l i else run r i

/-- The worst-case number of queries (comparisons) performed by the tree. -/
def depth : DecisionTree I O → ℕ
  | leaf _ => 0
  | node _ l r => max (depth l) (depth r) + 1

/-- A decision tree of depth `d` can produce at most `2 ^ d` distinct outputs. -/
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
theorem sorting_lb_3 (t : DecisionTree (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3)))
    (hcorrect : ∀ p : Equiv.Perm (Fin 3), t.run p = p) :
    Nat.clog 2 (Nat.factorial 3) ≤ t.depth := by
  classical
  have hcard : (Finset.univ.image t.run).card = 6 := by
    have huniv : Finset.univ.image t.run = (Finset.univ : Finset (Equiv.Perm (Fin 3))) :=
      Finset.eq_univ_of_forall fun p => Finset.mem_image.2 ⟨p, Finset.mem_univ _, hcorrect p⟩
    rw [huniv, Finset.card_univ]
    simp [Fintype.card_perm, Nat.factorial]
  have h := DecisionTree.card_image_run_le t Finset.univ
  rw [hcard] at h
  have hfac : Nat.factorial 3 ≤ 2 ^ t.depth := by simpa [Nat.factorial] using h
  exact (Nat.clog_le_iff_le_pow (by norm_num)).2 hfac

/-- The bound above really is the number `3`: `⌈log₂ (3!)⌉ = 3`. -/
theorem clog_two_factorial_three : Nat.clog 2 (Nat.factorial 3) = 3 := by decide

/-- The bound is attained: there is a correct depth-`3` decision tree for `3` elements,
so `sorting_lb_3` is not vacuous and is sharp. -/
theorem exists_sorting_tree_depth_three :
    ∃ t : DecisionTree (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3)),
      (∀ p, t.run p = p) ∧ t.depth = 3 := by
  classical
  obtain ⟨e⟩ : Nonempty (Equiv.Perm (Fin 3) ≃ Fin 6) := by
    refine ⟨Fintype.equivFinOfCardEq ?_⟩
    simp [Fintype.card_perm, Nat.factorial]
  refine ⟨DecisionTree.node (fun p => decide ((e p : ℕ) < 4))
    (DecisionTree.node (fun p => decide ((e p : ℕ) < 2))
      (DecisionTree.node (fun p => decide ((e p : ℕ) = 0))
        (DecisionTree.leaf (e.symm 0)) (DecisionTree.leaf (e.symm 1)))
      (DecisionTree.node (fun p => decide ((e p : ℕ) = 2))
        (DecisionTree.leaf (e.symm 2)) (DecisionTree.leaf (e.symm 3))))
    (DecisionTree.node (fun p => decide ((e p : ℕ) = 4))
      (DecisionTree.leaf (e.symm 4)) (DecisionTree.leaf (e.symm 5))),
    ?_, by simp [DecisionTree.depth]⟩
  intro p
  have hlt := (e p).isLt
  have key : ∀ k : Fin 6, (e p : ℕ) = (k : ℕ) → e.symm k = p := by
    intro k hk
    have hek : e p = k := Fin.ext hk
    rw [← hek, Equiv.symm_apply_apply]
  interval_cases h : ((e p : ℕ)) <;> simp [DecisionTree.run, h] <;> exact key _ (by omega)

end CS

