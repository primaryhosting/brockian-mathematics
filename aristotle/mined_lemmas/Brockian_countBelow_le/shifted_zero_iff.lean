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

theorem shifted_zero_iff (p h n : Nat) (hp : 0 < p) (hn : n < p) :
    ((n + h) % p = 0) ↔ n = excludedResidue p h := by
  have hr : h % p < p := Nat.mod_lt _ hp
  have hmod : (n + h) % p = (n + h % p) % p := by simp [Nat.add_mod]
  rw [hmod, excludedResidue]
  rcases Nat.eq_zero_or_pos (h % p) with h0 | h0
  · rw [h0]
    simp [Nat.mod_eq_of_lt hn, Nat.mod_self]
  · have hpr : p - h % p < p := by omega
    rw [Nat.mod_eq_of_lt hpr]
    rcases Nat.lt_or_ge (n + h % p) p with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · have hsub : (n + h % p) % p = n + h % p - p := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      rw [hsub]
      omega

/-- Boolean form of `shifted_zero_iff`. -/
