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

lemma fooling_card (p : Prot n) (S : Finset (Inp n × Inp n))
    (h1 : ∀ q ∈ S, p.eval q.1 q.2 = true)
    (h2 : ∀ q ∈ S, ∀ q' ∈ S, q ≠ q' → p.eval q.1 q'.2 = false ∨ p.eval q'.1 q.2 = false) :
    S.card ≤ 2 ^ p.depth := by
  classical
  induction p generalizing S with
  | leaf b =>
    simp only [Prot.depth, pow_zero]
    rw [Finset.card_le_one]
    intro a ha b' hb'
    by_contra hne
    have hb := h1 a ha
    simp only [Prot.eval] at hb
    rcases h2 a ha b' hb' hne with h | h <;> simp [Prot.eval, hb] at h
  | alice f p q ihp ihq =>
    have hcard : (S.filter (fun s => f s.1 = true)).card
        + (S.filter (fun s => ¬ (f s.1 = true))).card = S.card :=
      Finset.card_filter_add_card_filter_not _
    have hp : (S.filter (fun s => f s.1 = true)).card ≤ 2 ^ p.depth := by
      refine ihp _ ?_ ?_
      · intro s hs
        simp only [Finset.mem_filter] at hs
        have := h1 s hs.1
        simp only [Prot.eval, hs.2, if_true] at this
        exact this
      · intro s hs s' hs' hne
        simp only [Finset.mem_filter] at hs hs'
        have := h2 s hs.1 s' hs'.1 hne
        simp only [Prot.eval, hs.2, hs'.2, if_true] at this
        exact this
    have hq : (S.filter (fun s => ¬ (f s.1 = true))).card ≤ 2 ^ q.depth := by
      refine ihq _ ?_ ?_
      · intro s hs
        simp only [Finset.mem_filter, Bool.not_eq_true] at hs
        have := h1 s hs.1
        simp only [Prot.eval, hs.2] at this
        simpa using this
      · intro s hs s' hs' hne
        simp only [Finset.mem_filter, Bool.not_eq_true] at hs hs'
        have := h2 s hs.1 s' hs'.1 hne
        simp only [Prot.eval, hs.2, hs'.2] at this
        simpa using this
    have h1' : (2 : ℕ) ^ p.depth ≤ 2 ^ (max p.depth q.depth) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have h2' : (2 : ℕ) ^ q.depth ≤ 2 ^ (max p.depth q.depth) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    simp only [Prot.depth, pow_succ]
    omega
  | bob f p q ihp ihq =>
    have hcard : (S.filter (fun s => f s.2 = true)).card
        + (S.filter (fun s => ¬ (f s.2 = true))).card = S.card :=
      Finset.card_filter_add_card_filter_not _
    have hp : (S.filter (fun s => f s.2 = true)).card ≤ 2 ^ p.depth := by
      refine ihp _ ?_ ?_
      · intro s hs
        simp only [Finset.mem_filter] at hs
        have := h1 s hs.1
        simp only [Prot.eval, hs.2, if_true] at this
        exact this
      · intro s hs s' hs' hne
        simp only [Finset.mem_filter] at hs hs'
        have := h2 s hs.1 s' hs'.1 hne
        simp only [Prot.eval, hs.2, hs'.2, if_true] at this
        exact this
    have hq : (S.filter (fun s => ¬ (f s.2 = true))).card ≤ 2 ^ q.depth := by
      refine ihq _ ?_ ?_
      · intro s hs
        simp only [Finset.mem_filter, Bool.not_eq_true] at hs
        have := h1 s hs.1
        simp only [Prot.eval, hs.2] at this
        simpa using this
      · intro s hs s' hs' hne
        simp only [Finset.mem_filter, Bool.not_eq_true] at hs hs'
        have := h2 s hs.1 s' hs'.1 hne
        simp only [Prot.eval, hs.2, hs'.2] at this
        simpa using this
    have h1' : (2 : ℕ) ^ p.depth ≤ 2 ^ (max p.depth q.depth) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have h2' : (2 : ℕ) ^ q.depth ≤ 2 ^ (max p.depth q.depth) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    simp only [Prot.depth, pow_succ]
    omega

/-- **Deterministic lower bound.**  Any deterministic two-way protocol computing
set disjointness on an `n`-element ground set has communication cost `≥ n`. -/
