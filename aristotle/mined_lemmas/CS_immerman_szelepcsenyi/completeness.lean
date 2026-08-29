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

lemma completeness (hs : s < n) (hg : ∀ u v, g u v = true → u < n ∧ v < n)
    (h : reachB n g s n t = false) : Accepts n g s t := by
  have hphi : ∀ x, x < n → reachB n g s n x = true → x ≠ t ∧ g x t = false := by
    intro x hx hrx
    constructor
    · rintro rfl
      rw [h] at hrx
      exact Bool.noConfusion hrx
    · cases hgx : g x t with
      | false => rfl
      | true =>
          have ht : t < n := (hg _ _ hgx).2
          have : reachB n g s (n + 1) t = true :=
            (reachB_succ_iff n t).2 ⟨ht, x, hx, hrx, Or.inr hgx⟩
          rw [reachB_le_n hs this] at h
          exact Bool.noConfusion h
  have r1 : Relation.ReflTransGen (Step n g s t) init
      (.levelStart n (cnt (n := n) (g := g) (s := s) n)) := by
    have h0 : (init : St) = .levelStart 0 (cnt (n := n) (g := g) (s := s) 0) := by
      rw [cnt_zero hs]; rfl
    rw [h0]
    exact levels_run hs n 0 (by omega)
  have s1 : Step n g s t (.levelStart n (cnt (n := n) (g := g) (s := s) n))
      (.inner n (cnt (n := n) (g := g) (s := s) n) 0 t 0 0) := Step.startFinal
  have r2 := inner_run (t := t) (i := n) (j := t) (cnt (n := n) (g := g) (s := s) n) 0 hphi n 0
    (by omega)
  rw [cntUpto_zero] at r2
  have s2 : Step n g s t
      (.inner n (cnt (n := n) (g := g) (s := s) n) 0 t n (cnt (n := n) (g := g) (s := s) n))
      .acc := Step.innerAccept rfl
  exact ((r1.tail s1).trans r2).tail s2

end Machine

/-! ### Space bound: only polynomially many configurations are reachable

Every numeric component of a reachable configuration is `< n + 2`, so all reachable
configurations lie in a set of size at most `6 * (n + 2) ^ 8`; a machine with that many
configurations runs in space `O(log n)`. -/

/-- Assemble a configuration out of a tag and eight numbers. -/
