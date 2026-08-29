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

lemma reachB_of_reflTransGen (hs : s < n) (hg : ∀ u v, g u v = true → u < n ∧ v < n)
    {v : ℕ} (h : Relation.ReflTransGen (fun a b => g a b = true) s v) :
    reachB n g s n v = true := by
  have : ∃ m, reachB n g s m v = true := by
    induction h with
    | refl => exact ⟨0, by simp⟩
    | @tail b c _ hbc ih =>
        obtain ⟨m, hm⟩ := ih
        exact ⟨m + 1, (reachB_succ_iff m c).2
          ⟨(hg _ _ hbc).2, b, (hg _ _ hbc).1, hm, Or.inr hbc⟩⟩
  obtain ⟨m, hm⟩ := this
  exact reachB_le_n hs hm

