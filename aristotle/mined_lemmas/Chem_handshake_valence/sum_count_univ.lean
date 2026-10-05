/-
# Handshake Valence
Category: Chemistry
Target: Chem.handshake_valence
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Handshake Valence

The handshake (degree-sum) lemma in chemical language: for any molecule, the sum of the
valences of its atoms equals twice the number of its bonds, where a bond of order `k`
(double, triple, ...) is counted `k` times.
-/

namespace Chem

open Finset

/-- A molecular structure on a type of atoms `V`: a multiset of bonds, each bond being an
unordered pair of atoms.  Multiple bonds (double, triple, ...) are recorded as repeated
entries of the same pair, so `bonds` is a multiset rather than a set. -/
structure Molecule (V : Type*) where
  /-- The bonds of the molecule, as a multiset of unordered pairs of atoms. -/
  bonds : Multiset (Sym2 V)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The valence (degree) of an atom: the number of bond endpoints attached to it, so that a
bond of order `k` contributes `k` to each of its two atoms. -/

theorem sum_count_univ (s : Multiset V) :
    ∑ a : V, Multiset.count a s = Multiset.card s := by
  rw [← Multiset.toFinset_sum_count_eq s]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro a _ ha
  simpa using ha

/-- **Handshake lemma for valences.**  The sum of the valences of all atoms of a molecule
equals twice the number of its bonds (a double bond counting as two bonds, etc.). -/
