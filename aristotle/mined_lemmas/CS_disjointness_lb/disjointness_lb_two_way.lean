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

theorem disjointness_lb_two_way {N : ℕ} (hN : 0 < N) (P : Fin N → Prot n) (d : ℕ)
    (hd : ∀ r, (P r).depth ≤ d)
    (herr : ∀ x y : Inp n,
      4 ^ n * ((univ.filter (fun r => (P r).eval x y ≠ disj x y)).card) < N) :
    n ≤ d := by
  classical
  set bad : Inp n × Inp n → Finset (Fin N) :=
    fun q => univ.filter (fun r => (P r).eval q.1 q.2 ≠ disj q.1 q.2) with hbad
  set B : Finset (Fin N) := univ.biUnion bad with hB
  have hBcard : B.card ≤ ∑ q : Inp n × Inp n, (bad q).card := Finset.card_biUnion_le
  have h4 : (4 : ℕ) ^ n = 2 ^ n * 2 ^ n := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  have hpairs : (univ : Finset (Inp n × Inp n)).card = 4 ^ n := by
    rw [Finset.card_univ, Fintype.card_prod, h4]
    simp
  have hlt : ∀ q : Inp n × Inp n, 4 ^ n * (bad q).card < N := fun q => herr q.1 q.2
  have hsum : 4 ^ n * (∑ q : Inp n × Inp n, (bad q).card) ≤ 4 ^ n * (N - 1) := by
    rw [Finset.mul_sum]
    calc ∑ q : Inp n × Inp n, 4 ^ n * (bad q).card
        ≤ ∑ _q : Inp n × Inp n, (N - 1) := by
          refine Finset.sum_le_sum ?_
          intro q _
          have := hlt q
          omega
      _ = 4 ^ n * (N - 1) := by
          rw [Finset.sum_const, hpairs, smul_eq_mul]
  have hpos : 0 < (4 : ℕ) ^ n := pow_pos (by norm_num) n
  have hBlt : B.card < N := by
    have : (∑ q : Inp n × Inp n, (bad q).card) ≤ N - 1 := Nat.le_of_mul_le_mul_left hsum hpos
    omega
  obtain ⟨r, hr⟩ : ∃ r : Fin N, r ∉ B := by
    by_contra hcon
    push_neg at hcon
    have : (univ : Finset (Fin N)).card ≤ B.card :=
      Finset.card_le_card (fun r _ => hcon r)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  have hgood : ∀ x y : Inp n, (P r).eval x y = disj x y := by
    intro x y
    by_contra hne
    apply hr
    rw [hB]
    refine Finset.mem_biUnion.mpr ⟨(x, y), Finset.mem_univ _, ?_⟩
    simpa [hbad] using hne
  exact le_trans (disjointness_lb_deterministic (P r) hgood) (hd r)

end CS

