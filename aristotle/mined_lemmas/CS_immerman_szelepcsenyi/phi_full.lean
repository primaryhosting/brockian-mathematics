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
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace CS

/-! ## Reachability in a finite directed graph

We work with a directed graph on the vertex set `{0, 1, ..., n-1}` given by a Boolean
adjacency function `g`.  `reachB n g s i v` says that `v` is reachable from `s` by a walk of
length *at most* `i` (we allow "staying put" at each step, so walks of length exactly `i`
with lazy steps are the same thing as walks of length at most `i`). -/

section Graph

variable (n : ℕ) (g : ℕ → ℕ → Bool) (s : ℕ)

/-- `reachB n g s i v = true` iff `v` is reachable from `s` in at most `i` steps
(inside the vertex set `{0,…,n-1}`). -/

lemma phi_full {i j : ℕ} (h : cnt (n := n) (g := g) (s := s) i ≤ cntPhi n g s i j n)
    {x : ℕ} (hx : x < n) (hrx : reachB n g s i x = true) : x ≠ j ∧ g x j = false := by
  set A := (Finset.range n).filter
    (fun y => reachB n g s i y = true ∧ y ≠ j ∧ g y j = false) with hA
  set B := Rset (n := n) (g := g) (s := s) i with hB
  have hsub : A ⊆ B := by
    intro y hy
    simp only [hA, Finset.mem_filter, Finset.mem_range] at hy
    exact mem_Rset.2 ⟨hy.1, hy.2.1⟩
  have hcard : B.card ≤ A.card := h
  have : A = B := Finset.eq_of_subset_of_card_le hsub hcard
  have hxB : x ∈ B := mem_Rset.2 ⟨hx, hrx⟩
  rw [← this] at hxB
  simp only [hA, Finset.mem_filter, Finset.mem_range] at hxB
  exact hxB.2.2

/-- If all of `R_i` avoids `j` and is non-adjacent to `j`, then `j ∉ R_{i+1}`. -/
