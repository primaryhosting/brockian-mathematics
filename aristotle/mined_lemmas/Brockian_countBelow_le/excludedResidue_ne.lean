/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A *constellation* (or prime `k`-tuple pattern) is a tuple of integer shifts
`(h₁, …, h_k)`.  Its *local count* at a modulus `p` is the number of residues
`n` with `0 ≤ n < p` such that none of the shifted values `n + hᵢ` is divisible
by `p`.  This is the quantity `p - ν_p(H)` appearing in the singular series of
the Hardy–Littlewood prime `k`-tuple conjecture, where `ν_p(H)` is the number of
distinct residues occupied by the pattern mod `p`.

This file develops the local count from scratch and settles the case `k = 3`:
the local count of a triple equals `p` minus the number of *distinct* residues
among the three excluded classes `-hᵢ mod p`.  In particular a triple whose
shifts are pairwise incongruent mod `p` has local count exactly `p - 3`.

The development is self-contained (core Lean 4 only, no imports), so that the
required header comment can be the very first thing in the file.  (With Mathlib
available the same argument is the complement count
`Finset.card_univ_diff : (Finset.univ \ s).card = Fintype.card α - s.card`
together with `ZMod.card`, applied to the excluded set `{-h₁, -h₂, -h₃} ⊆ ZMod p`;
no single Mathlib lemma states the constellation local count itself.)
-/

namespace Brockian

/-! ## A counting operator -/

/-- `countBelow N f` is the number of naturals `n < N` with `f n = true`. -/

theorem excludedResidue_ne (p a b : Nat) (hp : 0 < p) (hab : a % p ≠ b % p) :
    excludedResidue p a ≠ excludedResidue p b := by
  have ha : a % p < p := Nat.mod_lt _ hp
  have hb : b % p < p := Nat.mod_lt _ hp
  unfold excludedResidue
  rcases Nat.eq_zero_or_pos (a % p) with h0 | h0 <;>
    rcases Nat.eq_zero_or_pos (b % p) with k0 | k0
  · omega
  · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [k0, Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega : p - a % p < p),
      Nat.mod_eq_of_lt (by omega : p - b % p < p)]
    omega

/-! ## The local count of a `3`-tuple -/

/-- `n` survives the constellation `(h1, h2, h3)` at `p` when none of the shifted
values `n + hᵢ` is divisible by `p`. -/
