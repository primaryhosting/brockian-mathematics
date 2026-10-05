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

theorem count_toMultiset_of_not_isDiag (e : Sym2 V) (he : ¬ e.IsDiag) (a : V) :
    Multiset.count a e.toMultiset = if a ∈ e then 1 else 0 := by
  induction e with
  | _ x y =>
    simp only [Sym2.isDiag_iff_proj_eq] at he
    simp only [Sym2.toMultiset, Sym2.mem_iff]
    rcases eq_or_ne a x with rfl | hax
    · simp [he]
    · rcases eq_or_ne a y with rfl | hay
      · simp [hax, Ne.symm hax]
      · simp [hax, hay]

/-- The molecule associated with a simple graph of single bonds. -/
