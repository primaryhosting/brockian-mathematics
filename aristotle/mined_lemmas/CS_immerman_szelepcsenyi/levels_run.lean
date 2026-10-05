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

lemma levels_run (hs : s < n) :
    ∀ (k i : ℕ), i + k = n →
      Relation.ReflTransGen (Step n g s t) (.levelStart i (cnt (n := n) (g := g) (s := s) i))
        (.levelStart n (cnt (n := n) (g := g) (s := s) n)) := by
  intro k
  induction k with
  | zero =>
      intro i hi
      obtain rfl : i = n := by omega
      exact Relation.ReflTransGen.refl
  | succ k ih =>
      intro i hi
      have hin : i < n := by omega
      have s1 : Step n g s t (.levelStart i (cnt (n := n) (g := g) (s := s) i))
          (.outer i (cnt (n := n) (g := g) (s := s) i) 0 0) := Step.startLevel hin
      have s2 := outer_run (g := g) (t := t) hs hin n 0 (by omega)
      rw [cntUpto_zero] at s2
      exact ((Relation.ReflTransGen.single s1).trans s2).trans (ih (i + 1) (by omega))

/-- **Completeness**: if `t` is not reachable from `s` then the machine accepts. -/
