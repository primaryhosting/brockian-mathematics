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

def multiValence (bonds : Multiset (Atom × Atom)) (a : Atom) : ℕ :=
  (bonds.map fun b => (if b.1 = a then 1 else 0) + (if b.2 = a then 1 else 0)).sum

/-- **Handshake lemma for valences, with bond multiplicities.**  The sum of the atomic
valences equals twice the number of bonds counted with multiplicity. -/
