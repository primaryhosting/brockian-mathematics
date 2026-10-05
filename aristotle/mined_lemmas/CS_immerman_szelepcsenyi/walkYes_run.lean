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

lemma walkYes_run (i c d j : ℕ) :
    ∀ (r a m : ℕ), reachB n g s r a = true →
      Relation.ReflTransGen (Step n g s t) (.walkYes i c d j s (r + m)) (.walkYes i c d j a m) := by
  intro r
  induction r with
  | zero =>
      intro a m h
      simp only [reachB_zero, beq_iff_eq] at h
      subst h
      rw [Nat.zero_add]
  | succ r ih =>
      intro a m h
      obtain ⟨ha, u, -, hru, hstep⟩ := (reachB_succ_iff r a).1 h
      have h1 := ih u (m + 1) hru
      rw [show r + (m + 1) = r + 1 + m by omega] at h1
      exact h1.tail (Step.walkYesStep ha hstep)

/-- Guessing a walk certifying membership in `R_r`, inside the `walkIn` phase. -/
