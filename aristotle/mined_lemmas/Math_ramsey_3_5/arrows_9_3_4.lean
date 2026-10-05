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
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open SimpleGraph Finset

/-- `Arrows N s t` says that every simple graph on at least `N` vertices contains
either a clique of size `s` or an independent set of size `t`
(i.e. `N → (s, t)` in the arrow notation for Ramsey numbers). -/

lemma arrows_9_3_4 : Arrows 9 3 4 := by
  apply arrows_of_card_eq
  intro V _ G hcard h1 h2
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  -- Every vertex has degree exactly 3.
  have hdeg : ∀ v : V, G.degree v = 3 := by
    intro v
    set A : Finset V := univ.filter (fun x => G.Adj v x) with hAdef
    set B : Finset V := univ.filter (fun x => x ≠ v ∧ ¬ G.Adj v x) with hBdef
    have hdegA : G.degree v = A.card := by
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
    have hsplit : A.card + B.card + 1 = Fintype.card V := by
      have h0 : A.card + (univ.filter (fun x => ¬ G.Adj v x)).card = Fintype.card V := by
        rw [hAdef]
        simpa using Finset.card_filter_add_card_filter_not
          (s := (univ : Finset V)) (p := fun x => G.Adj v x)
      have h1' : (univ.filter (fun x => ¬ G.Adj v x)) = insert v B := by
        ext x
        by_cases hx : x = v
        · subst hx; simp [hBdef]
        · simp [hBdef, hx]
      have h2' : v ∉ B := by simp [hBdef]
      rw [h1', Finset.card_insert_of_notMem h2'] at h0
      omega
    have hub : A.card ≤ 3 := by
      by_contra hgt
      push_neg at hgt
      exact red_extend (m := 4) (s := 2) (t := 3) (arrows_two_left 4) G v A
        (fun x hx => by simpa [hAdef] using hx) (by omega) h1 h2
    have hlb : 3 ≤ A.card := by
      by_contra hlt
      push_neg at hlt
      exact blue_extend (n := 6) (s := 2) (t := 3) arrows_6_3_3 G v B
        (fun x hx => by simpa [hBdef] using hx) (by omega) h1 h2
    omega
  -- Handshake: the degree sum is odd, contradiction.
  have hsum : ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G
  rw [Finset.sum_congr rfl (fun v _ => hdeg v)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, hcard] at hsum
  omega

/-! ### `R(3,5) ≤ 14` -/

