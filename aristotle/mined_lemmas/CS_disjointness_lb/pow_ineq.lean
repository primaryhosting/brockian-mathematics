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

lemma pow_ineq (m N : ℕ) (h : 6 * m < N) : 16 ^ (N + m) ≤ 27 ^ N := by
  obtain ⟨t, ht⟩ : ∃ t, N = 6 * m + 1 + t := ⟨N - (6 * m + 1), by omega⟩
  subst ht
  have h1 : (16 : ℕ) ^ 7 ≤ 27 ^ 6 := by norm_num
  have h2 : ((16 : ℕ) ^ 7) ^ m ≤ (27 ^ 6) ^ m := Nat.pow_le_pow_left h1 m
  have h3 : (16 : ℕ) ^ t ≤ 27 ^ t := Nat.pow_le_pow_left (by norm_num) t
  have e1 : (16 : ℕ) ^ (6 * m + 1 + t + m) = 16 * ((16 ^ 7) ^ m * 16 ^ t) := by
    rw [← pow_mul]
    ring
  have e2 : (27 : ℕ) ^ (6 * m + 1 + t) = 27 * ((27 ^ 6) ^ m * 27 ^ t) := by
    rw [← pow_mul]
    ring
  rw [e1, e2]
  have : ((16 : ℕ) ^ 7) ^ m * 16 ^ t ≤ (27 ^ 6) ^ m * 27 ^ t := Nat.mul_le_mul h2 h3
  calc 16 * (((16 : ℕ) ^ 7) ^ m * 16 ^ t) ≤ 16 * ((27 ^ 6) ^ m * 27 ^ t) := by
        exact Nat.mul_le_mul_left _ this
    _ ≤ 27 * ((27 ^ 6) ^ m * 27 ^ t) := by
        exact Nat.mul_le_mul_right _ (by norm_num)

/-! ### Randomised one-way protocols -/

/-- A deterministic one-way protocol with `c` bits of communication: Alice sends
a `c`-bit message `msg x`, and Bob outputs `out (msg x) y`. -/
structure OneWay (n c : ℕ) where
  msg : Inp n → Fin (2 ^ c)
  out : Fin (2 ^ c) → Inp n → Bool

/-- The output of a one-way protocol. -/
