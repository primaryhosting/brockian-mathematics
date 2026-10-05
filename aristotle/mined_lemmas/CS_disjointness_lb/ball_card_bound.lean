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

lemma ball_card_bound (z : Inp n) (S : Finset (Inp n)) (k : ℕ)
    (hS : ∀ x ∈ S, ((univ.filter (fun i => x i ≠ z i)).card) ≤ k) :
    3 ^ (n - k) * S.card ≤ 4 ^ n := by
  have hagree : ∀ x ∈ S, 3 ^ (n - k) ≤ 3 ^ ((univ.filter (fun i => x i = z i)).card) := by
    intro x hx
    have hsplit : (univ.filter (fun i => x i = z i)).card
        + (univ.filter (fun i => ¬ (x i = z i))).card = (univ : Finset (Fin n)).card :=
      Finset.card_filter_add_card_filter_not _
    have hcard : (univ : Finset (Fin n)).card = n := by simp
    have := hS x hx
    have hle : n - k ≤ (univ.filter (fun i => x i = z i)).card := by
      simp only [ne_eq] at this
      omega
    exact Nat.pow_le_pow_right (by norm_num) hle
  calc 3 ^ (n - k) * S.card = ∑ _x ∈ S, 3 ^ (n - k) := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ x ∈ S, 3 ^ ((univ.filter (fun i => x i = z i)).card) :=
        Finset.sum_le_sum hagree
    _ ≤ ∑ x : Inp n, 3 ^ ((univ.filter (fun i => x i = z i)).card) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 4 ^ n := agree_sum z

/-! ### An arithmetic lemma -/

