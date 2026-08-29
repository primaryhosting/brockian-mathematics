/-
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

universe u

variable {V : Type u}

/-! ## Walks and shortest-path distances

A weighted directed graph on the vertex type `V` is given by a weight function
`w : V → V → ℝ≥0∞`; the value `⊤` means "no edge", and all weights are nonnegative
by construction.  A walk starting at `a` is described by the list `l` of the vertices
it visits after `a`; its endpoint is `l.getLastD a`. -/

/-- The cost of the walk that starts at `a` and then visits the vertices of `l` in order. -/

lemma iterate_inv (w : V → V → ℝ≥0∞) (s : V) (k : ℕ) :
    Inv w s ((step w)^[k] (initState s)) ∧
      (((step w)^[k] (initState s)).visited = Finset.univ ∨
        ((step w)^[k] (initState s)).visited.card = k) := by
  induction k with
  | zero => exact ⟨inv_init w s, Or.inr (by simp [initState])⟩
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨inv_step w s _ ih.1, card_step w _ k ih.2⟩

/-- **Correctness of Dijkstra's algorithm.**  For a finite directed graph with
nonnegative edge weights (encoded by `w : V → V → ℝ≥0∞`, where `⊤` means "no edge"),
the distance array computed by Dijkstra's algorithm from the source `s` equals the
shortest-path distance from `s`, i.e. the infimum of the costs of all walks from `s`. -/
