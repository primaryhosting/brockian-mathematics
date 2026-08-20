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

/-
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Polignac's conjecture (1849) asserts that for every positive even number `n` there are
infinitely many pairs of *consecutive* primes `p < q` with `q - p = n`.  This is open
(the case `n = 2` is the twin prime conjecture).

This file gives a Lean-checked *conditional reduction*: Polignac's conjecture follows from
Dickson's conjecture for two linear forms `M x + a`, `M x + b` (the standard hypothesis that an
admissible system of linear forms simultaneously represents primes infinitely often).

The reduction is the classical sieve/congruence argument: given an even `n`, one produces an
arithmetic progression `M x + a` such that *all* of the intermediate values
`M x + a + 1, …, M x + a + (n-1)` are automatically composite, while the two forms
`M x + a` and `M x + a + n` are admissible.
-/

namespace Brockian.PolignacPrimes

/-- `q` is the prime immediately following `p`: both are prime, `p < q`, and nothing strictly
between them is prime. -/

theorem exists_not_dvd_pair {p u c d : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u)
    (hpar : c % 2 = d % 2) :
    ∃ x : ℕ, ¬ p ∣ (u * x + c) ∧ ¬ p ∣ (u * x + d) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hu' : (u : ZMod p) ≠ 0 := by
    simpa [ZMod.natCast_eq_zero_iff] using hu
  set S : Finset (ZMod p) := {0, (c : ZMod p) - (d : ZMod p)} with hS
  have hcard : S.card < Fintype.card (ZMod p) := by
    rw [ZMod.card p]
    rcases eq_or_lt_of_le hp.two_le with h2 | h2
    · -- `p = 2`, and by the parity assumption the two bad residues coincide
      have hp2 : p = 2 := h2.symm
      subst hp2
      have : (c : ZMod 2) = (d : ZMod 2) := by
        rw [← ZMod.natCast_mod c 2, ← ZMod.natCast_mod d 2, hpar]
      simp [hS, this]
    · exact lt_of_le_of_lt (Finset.card_insert_le _ _) (by simpa using h2)
  obtain ⟨w, hw⟩ : ∃ w : ZMod p, w ∉ S := by
    by_contra hc
    push_neg at hc
    have : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hc
    simp [this] at hcard
  have hw0 : w ≠ 0 := by
    intro h; exact hw (by simp [hS, h])
  have hwcd : w ≠ (c : ZMod p) - (d : ZMod p) := by
    intro h; exact hw (by simp [hS, h])
  refine ⟨((w - (c : ZMod p)) * (u : ZMod p)⁻¹).val, ?_, ?_⟩
  · intro hdvd
    have : ((u * ((w - (c : ZMod p)) * (u : ZMod p)⁻¹).val + c : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id] at this
    field_simp at this
    exact hw0 (by linear_combination this)
  · intro hdvd
    have : ((u * ((w - (c : ZMod p)) * (u : ZMod p)⁻¹).val + d : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id] at this
    field_simp at this
    apply hwcd
    linear_combination this

/-- For even `n` and any bound `N`, there is a positive `m` such that no prime `p ≤ N` divides
either `m` or `m + n`.  (A Chinese-remainder style avoidance argument.) -/
