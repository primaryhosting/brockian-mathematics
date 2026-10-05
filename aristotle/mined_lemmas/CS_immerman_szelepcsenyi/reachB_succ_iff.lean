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

lemma reachB_succ_iff (i v : ℕ) :
    reachB n g s (i + 1) v = true ↔
      v < n ∧ ∃ u, u < n ∧ reachB n g s i u = true ∧ (u = v ∨ g u v = true) := by
  constructor
  · intro h
    rw [reachB] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
      beq_iff_eq, Bool.or_eq_true] at h
    obtain ⟨hv, u, hu, h1, h2⟩ := h
    exact ⟨hv, u, hu, h1, h2⟩
  · rintro ⟨hv, u, hu, h1, h2⟩
    rw [reachB]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
      beq_iff_eq, Bool.or_eq_true]
    exact ⟨hv, u, hu, h1, h2⟩

