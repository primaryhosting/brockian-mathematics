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

theorem countBelow_three (p r1 r2 r3 : Nat) (h1 : r1 < p) (h2 : r2 < p) (h3 : r3 < p) :
    countBelow p (fun n => (n == r1) || (n == r2) || (n == r3)) = distinctCount3 r1 r2 r3 := by
  by_cases e12 : r1 = r2 <;> by_cases e13 : r1 = r3 <;> by_cases e23 : r2 = r3 <;>
    simp only [distinctCount3, e12, e13, e23]
  all_goals try omega
  · subst e12; subst e13
    simp only [Bool.or_self]
    rw [countBelow_singleton, if_pos h1]
    simp
  · subst e12
    have hfun : (fun n => (n == r1) || (n == r1) || (n == r3))
        = (fun n => (n == r1) || (n == r3)) := by
      funext n; simp
    rw [hfun, countBelow_pair p r1 r3 h1 h3 e13]
    simp
  · subst e13
    have hfun : (fun n => (n == r1) || (n == r2) || (n == r1))
        = (fun n => (n == r1) || (n == r2)) := by
      funext n; by_cases hn : n = r1 <;> by_cases hn2 : n = r2 <;> simp_all
    rw [hfun, countBelow_pair p r1 r2 h1 h2 e12, if_neg e12]
    simp
  · subst e23
    have hfun : (fun n => (n == r1) || (n == r2) || (n == r2))
        = (fun n => (n == r1) || (n == r2)) := by
      funext n; simp
    rw [hfun, countBelow_pair p r1 r2 h1 h2 e12]
    simp
  · rw [countBelow_or_disjoint p _ _
      (by intro n hn
          simp only [Bool.or_eq_true, beq_iff_eq] at hn ⊢
          rcases hn with rfl | rfl <;> simp_all),
      countBelow_singleton, if_pos h3, countBelow_pair p r1 r2 h1 h2 e12]
    simp

/-! ## Excluded residues of a shift -/

/-- The unique residue `n` mod `p` that the shift `h` kills, i.e. with `p ∣ n + h`. -/
