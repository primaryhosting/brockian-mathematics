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

lemma inner_run {i j : ℕ} (c d : ℕ)
    (hphi : ∀ x, x < n → reachB n g s i x = true → x ≠ j ∧ g x j = false) :
    ∀ (k u : ℕ), u + k = n →
      Relation.ReflTransGen (Step n g s t) (.inner i c d j u (cntUpto n g s i u))
        (.inner i c d j n (cnt (n := n) (g := g) (s := s) i)) := by
  intro k
  induction k with
  | zero =>
      intro u hu
      obtain rfl : u = n := by omega
      rw [cntUpto_n]
  | succ k ih =>
      intro u hu
      have hun : u < n := by omega
      by_cases hr : reachB n g s i u = true
      · obtain ⟨hne, hgj⟩ := hphi u hun hr
        have s1 : Step n g s t (.inner i c d j u (cntUpto n g s i u))
            (.walkIn i c d j u (cntUpto n g s i u) s i) := Step.innerCert hun
        have s2 := walkIn_run (t := t) i c d j u (cntUpto n g s i u) i u 0 hr
        rw [Nat.add_zero] at s2
        have s3 : Step n g s t (.walkIn i c d j u (cntUpto n g s i u) u 0)
            (.inner i c d j (u + 1) (cntUpto n g s i u + 1)) := Step.walkInDone rfl hne hgj
        have s4 := ih (u + 1) (by omega)
        rw [cntUpto_succ_pos hr] at s4
        exact ((Relation.ReflTransGen.single s1).trans s2).tail s3 |>.trans s4
      · have s1 : Step n g s t (.inner i c d j u (cntUpto n g s i u))
            (.inner i c d j (u + 1) (cntUpto n g s i u)) := Step.innerSkip hun
        have s4 := ih (u + 1) (by omega)
        rw [cntUpto_succ_neg hr] at s4
        exact (Relation.ReflTransGen.single s1).trans s4

/-- One pass of the outer loop computes `|R_{i+1}|` from `|R_i|`. -/
