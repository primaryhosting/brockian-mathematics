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

theorem immerman_szelepcsenyi {n : ℕ} {g : ℕ → ℕ → Bool} {s t : ℕ}
    (hs : s < n) (ht : t < n) (hgr : ∀ u v, g u v = true → u < n ∧ v < n) :
    (Accepts n g s t ↔ ¬ Relation.ReflTransGen (fun a b => g a b = true) s t) ∧
      (∀ w, Relation.ReflTransGen (Step n g s t) init w → w ∈ Box (n + 2)) ∧
      (Box (n + 2)).card ≤ 6 * (n + 2) ^ 8 := by
  refine ⟨⟨?_, ?_⟩, ?_, card_Box_le _⟩
  · intro hacc hreach
    have h1 : reachB n g s n t = false := soundness hs hacc
    have h2 : reachB n g s n t = true := reachB_of_reflTransGen hs hgr hreach
    rw [h1] at h2
    exact Bool.noConfusion h2
  · intro hno
    refine completeness hs hgr ?_
    cases hb : reachB n g s n t with
    | false => rfl
    | true => exact absurd (reflTransGen_of_reachB hb) hno
  · intro w hw
    exact mem_Box_of_Inv hs ht (Inv_of_reachable hs hw)

/-! ## Complementing an arbitrary finite configuration graph

The same statement for a nondeterministic machine whose configurations form an arbitrary finite
type (rather than an initial segment of `ℕ`). -/

section ConfigGraph

variable {V : Type} [Fintype V]

/-- Encoding of a configuration as a number `< Fintype.card V`. -/
