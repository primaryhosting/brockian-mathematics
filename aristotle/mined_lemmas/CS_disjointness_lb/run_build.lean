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

import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u v

/-- A deterministic two-party communication protocol: a binary tree whose internal nodes
are labelled either by a bit that Alice sends (a function of her input `x : X`) or by a bit
that Bob sends (a function of his input `y : Y`), and whose leaves carry the output bit. -/
inductive Protocol (X : Type u) (Y : Type v) : Type (max u v)
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → Protocol X Y → Protocol X Y → Protocol X Y
  | bob : (Y → Bool) → Protocol X Y → Protocol X Y → Protocol X Y

namespace Protocol

variable {X : Type u} {Y : Type v}

/-- The communication cost of a protocol: the depth of the tree, i.e. the worst-case number
of bits exchanged. -/

theorem run_build {n : ℕ} : ∀ (l : List (Fin n)) (acc S T : Finset (Fin n)),
    (build l acc).run S T = Disj n (acc ∪ S.filter (fun x => x ∈ l)) T := by
  intro l
  induction l with
  | nil =>
      intro acc S T
      simp only [build, run]
      have hemp : S.filter (fun x => x ∈ ([] : List (Fin n))) = ∅ := by simp
      rw [hemp, Finset.union_empty]
      by_cases h : Disj n acc T = true
      · rw [if_pos h, h]
      · simp only [Bool.not_eq_true] at h
        rw [h]
        simp
  | cons a l ih =>
      intro acc S T
      simp only [build, run]
      by_cases ha : a ∈ S
      · have hset : insert a acc ∪ S.filter (fun x => x ∈ l)
            = acc ∪ S.filter (fun x => x ∈ a :: l) := by
          ext x
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_filter, List.mem_cons]
          aesop
        rw [if_pos (by simp [ha] : decide (a ∈ S) = true), ih, hset]
      · have hset : acc ∪ S.filter (fun x => x ∈ l)
            = acc ∪ S.filter (fun x => x ∈ a :: l) := by
          ext x
          simp only [Finset.mem_union, Finset.mem_filter, List.mem_cons]
          aesop
        rw [if_neg (by simp [ha] : ¬ (decide (a ∈ S) = true)), ih, hset]

end Protocol

/-- **Matching upper bound.**  There is a deterministic protocol of cost `n + 1` computing
set disjointness on subsets of an `n`-element ground set; in particular the hypotheses of
`CS.disjointness_lb` are satisfiable and the `Ω(n)` bound is tight up to one bit. -/
