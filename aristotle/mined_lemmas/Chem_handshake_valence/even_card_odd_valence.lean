/-
# Handshake Valence
Category: Chemistry
Target: Chem.handshake_valence
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset

/-- A molecule, modelled as a finite bonding graph on a type of atoms: `bonds a b` holds
when atoms `a` and `b` are joined by a (single) chemical bond. -/
abbrev Molecule (Atom : Type*) := SimpleGraph Atom

variable {Atom : Type*} [Fintype Atom] (M : Molecule Atom) [DecidableRel M.Adj]

/-- The valence of an atom in a molecule: the number of bonds incident to it,
i.e. its degree in the bonding graph. -/

theorem even_card_odd_valence :
    Even ((univ.filter fun a : Atom => Odd (valence M a)).card) := by
  simpa [valence, Finset.filter_congr_decidable] using M.even_card_odd_degree_vertices

/-!
## A version allowing multiple bonds

Real molecules have double and triple bonds, which the simple-graph model cannot express.
Modelling the bond list as a multiset of (unordered) atom pairs, a bond of order `k` being
listed `k` times, the same identity holds.
-/

section Multi

variable {Atom : Type*} [Fintype Atom] [DecidableEq Atom]

/-- The valence of an atom `a` given a list of bonds (with multiplicity): each bond counts
once for each of its two ends equal to `a`. -/
