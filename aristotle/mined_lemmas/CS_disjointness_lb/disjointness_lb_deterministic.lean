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
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalise lower bounds on the communication complexity of set disjointness
`DISJ_n` on `n`-element ground sets.

* `CS.disjointness_lb` : the main target.  Any *public-coin randomised one-way*
  protocol that computes `DISJ_n` with error probability at most `1/8` on every
  input must communicate `c` bits with `n ≤ 6 * (c + 1)`, i.e. `c = Ω(n)`.
* `CS.disjointness_lb_deterministic` : any *deterministic two-way* protocol
  computing `DISJ_n` has depth (communication cost) at least `n`.
* `CS.disjointness_lb_two_way` : any randomised two-way protocol whose error
  probability on each input is smaller than `4 ^ (-n)` has depth at least `n`.
* `CS.disjointness_upper` : the hypotheses are not vacuous — a one-way protocol
  with `n` bits of communication and zero error always exists.

The proof of the main theorem is the standard argument: averaging over the public
randomness fixes a deterministic one-way protocol that is correct on average over
the hard distribution (`x` uniform, `y` a uniformly random singleton `{i}`); the
protocol's message determines a decoding `z` of Alice's input, so most inputs `x`
lie in a Hamming ball of radius `n / 4` around one of the `2 ^ c` decodings, and a
volume bound for Hamming balls forces `2 ^ c` to be exponentially large in `n`.
Note that `DISJ (x, {i}) = ¬ x i`, i.e. the index function reduces to disjointness.
-/

open Finset

namespace CS

/-- Inputs: subsets of `Fin n`, encoded as Boolean vectors. -/
abbrev Inp (n : ℕ) := Fin n → Bool

variable {n : ℕ}

/-- Set disjointness: `true` iff the two subsets of `Fin n` are disjoint. -/

theorem disjointness_lb_deterministic (p : Prot n) (hp : ∀ x y : Inp n, p.eval x y = disj x y) :
    n ≤ p.depth := by
  classical
  set S : Finset (Inp n × Inp n) :=
    Finset.image (fun x : Inp n => (x, fun i => !(x i))) univ with hS
  have hinj : Function.Injective (fun x : Inp n => (x, fun i => !(x i))) := by
    intro a b h
    exact congrArg Prod.fst h
  have hcard : S.card = 2 ^ n := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_univ]
    simp
  have key : S.card ≤ 2 ^ p.depth := by
    refine fooling_card p S ?_ ?_
    · intro q hq
      simp only [hS, Finset.mem_image, Finset.mem_univ, true_and] at hq
      obtain ⟨x, rfl⟩ := hq
      simp only [hp, disj, decide_eq_true_eq]
      intro i
      cases hx : x i <;> simp
    · intro q hq q' hq' hne
      simp only [hS, Finset.mem_image, Finset.mem_univ, true_and] at hq hq'
      obtain ⟨x, rfl⟩ := hq
      obtain ⟨x', rfl⟩ := hq'
      have hxx : x ≠ x' := by
        intro h
        exact hne (by rw [h])
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ x' i := by
        by_contra hcon
        push_neg at hcon
        exact hxx (funext hcon)
      simp only [hp]
      cases hx : x i with
      | false =>
        right
        have hx' : x' i = true := by
          rw [hx] at hi
          simpa using Ne.symm hi
        simp only [disj, decide_eq_false_iff_not]
        push_neg
        exact ⟨i, by simp [hx'], by simp [hx]⟩
      | true =>
        left
        have hx' : x' i = false := by
          rw [hx] at hi
          simpa using Ne.symm hi
        simp only [disj, decide_eq_false_iff_not]
        push_neg
        exact ⟨i, by simp [hx], by simp [hx']⟩
  rw [hcard] at key
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp key

/-- **Randomised two-way protocols with tiny error.**  Any randomised two-way
protocol whose error probability on every input is smaller than `4 ^ (-n)` has
communication cost at least `n`. -/
