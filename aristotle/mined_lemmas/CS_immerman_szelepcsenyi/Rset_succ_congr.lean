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

lemma Rset_succ_congr {a b : ℕ}
    (h : Rset (n := n) (g := g) (s := s) a = Rset (n := n) (g := g) (s := s) b) :
    Rset (n := n) (g := g) (s := s) (a + 1) = Rset (n := n) (g := g) (s := s) (b + 1) := by
  have key : ∀ u, u < n → (reachB n g s a u = true ↔ reachB n g s b u = true) := by
    intro u hu
    constructor
    · intro hau
      have : u ∈ Rset (n := n) (g := g) (s := s) b := by rw [← h, mem_Rset]; exact ⟨hu, hau⟩
      exact (mem_Rset.1 this).2
    · intro hbu
      have : u ∈ Rset (n := n) (g := g) (s := s) a := by rw [h, mem_Rset]; exact ⟨hu, hbu⟩
      exact (mem_Rset.1 this).2
  ext v
  simp only [mem_Rset, reachB_succ_iff]
  constructor
  · rintro ⟨hv, -, u, hu, h1, h2⟩
    exact ⟨hv, hv, u, hu, (key u hu).1 h1, h2⟩
  · rintro ⟨hv, -, u, hu, h1, h2⟩
    exact ⟨hv, hv, u, hu, (key u hu).2 h1, h2⟩

