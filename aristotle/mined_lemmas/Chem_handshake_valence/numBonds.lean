import Mathlib

/-!
# Handshake Valence
Category: Chemistry
Target: Chem.handshake_valence
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- A molecule (with single bonds only, and no self-bonds) modelled as a simple graph
whose vertices are the atoms and whose edges are the chemical bonds. -/
abbrev Molecule (Atom : Type*) := SimpleGraph Atom

variable {Atom : Type*} [Fintype Atom] (M : Molecule Atom) [DecidableRel M.Adj]

/-- The valence of an atom in a molecule: the number of bonds incident to it. -/

def numBonds : ℕ := M.edgeFinset.card

/-- **Handshake lemma for valences.** The sum of the atomic valences (vertex degrees)
in a molecule equals twice the number of bonds (edges).

This is Mathlib's `SimpleGraph.sum_degrees_eq_twice_card_edges`. -/
