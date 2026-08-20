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

theorem ConstellationLocalCountK3_of_distinct (p h1 h2 h3 : Nat) (hp : 0 < p)
    (d12 : h1 % p ≠ h2 % p) (d13 : h1 % p ≠ h3 % p) (d23 : h2 % p ≠ h3 % p) :
    localCountK3 p h1 h2 h3 = p - 3 := by
  rw [ConstellationLocalCountK3 p h1 h2 h3 hp]
  have n12 := excludedResidue_ne p h1 h2 hp d12
  have n13 := excludedResidue_ne p h1 h3 hp d13
  have n23 := excludedResidue_ne p h2 h3 hp d23
  simp only [distinctCount3, if_neg n12, if_neg n13, if_neg n23]

/-- Sanity check: the admissible triple `(0, 2, 6)` occupies three distinct residues
mod `5`, leaving `5 - 3 = 2` surviving classes. -/
example : localCountK3 5 0 2 6 = 2 := by decide

/-- Sanity check: mod `2` the triple `(0, 2, 6)` occupies a single residue, so the
local count is `2 - 1 = 1`. -/
example : localCountK3 2 0 2 6 = 1 := by decide

end Brockian

