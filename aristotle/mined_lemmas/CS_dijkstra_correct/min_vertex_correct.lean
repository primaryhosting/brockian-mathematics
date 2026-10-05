/-
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-!
## Setting

A weighted digraph on a finite vertex type `V` is given by a weight function
`w : V → V → ℕ∞`.  Weights live in `ℕ∞ = WithTop ℕ`, so they are automatically
nonnegative, and `w x y = ⊤` encodes "there is no edge from `x` to `y`".
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `RWalk w S s v l`: there is a walk from `s` to `v` of total weight `l`
all of whose vertices, **except possibly the final vertex `v`**, lie in `S`. -/
inductive RWalk (w : V → V → ℕ∞) (S : Finset V) (s : V) : V → ℕ∞ → Prop
  | nil : RWalk w S s s 0
  | cons {x v : V} {l : ℕ∞} : RWalk w S s x l → x ∈ S → RWalk w S s v (l + w x v)

/-- `Walk w s v l`: there is a walk from `s` to `v` of total weight `l`
(no restriction on the intermediate vertices). -/

theorem min_vertex_correct (w : V → V → ℕ∞) (s : V) (Q : Finset V) (d : V → ℕ∞)
    (hd : Inv w s Qᶜ d) (u : V) (hmin : ∀ v ∈ Q, d u ≤ d v) :
    ∀ (v : V) (l : ℕ∞), Walk w s v l → v ∈ Q → d u ≤ l := by
  intro v l h
  induction h with
  | nil =>
      intro hs
      exact le_trans (hmin _ hs) (hd.lb _ 0 RWalk.nil)
  | @cons x v l hxw _ ih =>
      intro hv
      by_cases hxS : x ∈ Qᶜ
      · have hdx : d x ≤ l := hd.final x hxS l hxw
        by_cases hdxtop : d x = ⊤
        · rw [hdxtop] at hdx
          have : l = ⊤ := top_le_iff.mp hdx
          simp [this]
        · have h1 : RWalk w Qᶜ s v (d x + w x v) := (hd.attained x hdxtop).cons hxS
          have h2 : d v ≤ d x + w x v := hd.lb _ _ h1
          calc d u ≤ d v := hmin _ hv
            _ ≤ d x + w x v := h2
            _ ≤ l + w x v := by gcongr
      · have hxQ : x ∈ Q := by simpa using hxS
        exact le_trans (ih hxQ) le_self_add

/-- One round of Dijkstra's algorithm preserves the loop invariant. -/
