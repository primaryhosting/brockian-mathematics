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

lemma outer_run (hs : s < n) {i : ℕ} (hi : i < n) :
    ∀ (k j : ℕ), j + k = n →
      Relation.ReflTransGen (Step n g s t)
        (.outer i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j) j)
        (.levelStart (i + 1) (cnt (n := n) (g := g) (s := s) (i + 1))) := by
  intro k
  induction k with
  | zero =>
      intro j hj
      obtain rfl : j = n := by omega
      rw [cntUpto_n]
      exact Relation.ReflTransGen.single Step.outerDone
  | succ k ih =>
      intro j hj
      have hjn : j < n := by omega
      by_cases hr : reachB n g s (i + 1) j = true
      · have s1 : Step n g s t
            (.outer i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j) j)
            (.walkYes i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j) j s (i + 1)) :=
          Step.outerYes hjn
        have s2 := walkYes_run (t := t) i (cnt (n := n) (g := g) (s := s) i)
          (cntUpto n g s (i + 1) j) j (i + 1) j 0 hr
        rw [Nat.add_zero] at s2
        have s3 : Step n g s t
            (.walkYes i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j) j j 0)
            (.outer i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j + 1) (j + 1)) :=
          Step.walkYesDone rfl
        have s4 := ih (j + 1) (by omega)
        rw [cntUpto_succ_pos hr] at s4
        exact ((Relation.ReflTransGen.single s1).trans s2).tail s3 |>.trans s4
      · have hphi : ∀ x, x < n → reachB n g s i x = true → x ≠ j ∧ g x j = false := by
          intro x hx hrx
          constructor
          · rintro rfl
            exact hr (reachB_mono hs hrx)
          · cases hgx : g x j with
            | false => rfl
            | true =>
                exact absurd ((reachB_succ_iff i j).2 ⟨hjn, x, hx, hrx, Or.inr hgx⟩) hr
        have s1 : Step n g s t
            (.outer i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j) j)
            (.inner i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j) j 0 0) :=
          Step.outerNo hjn
        have s2 := inner_run (t := t) (i := i) (j := j) (cnt (n := n) (g := g) (s := s) i)
          (cntUpto n g s (i + 1) j) hphi n 0 (by omega)
        rw [cntUpto_zero] at s2
        have s3 : Step n g s t
            (.inner i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j) j n
              (cnt (n := n) (g := g) (s := s) i))
            (.outer i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j) (j + 1)) :=
          Step.innerDone hi rfl
        have s4 := ih (j + 1) (by omega)
        rw [cntUpto_succ_neg hr] at s4
        exact ((Relation.ReflTransGen.single s1).trans s2).tail s3 |>.trans s4

/-- All the level counts can be computed, one level at a time. -/
