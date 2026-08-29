/-
# Handshake Valence
Category: Chemistry
Target: Chem.handshake_valence
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

/-- A molecule (or, more generally, any bonded structure) is recorded as a
multiset of bonds, each bond being an unordered pair of atoms.  Using a
multiset lets multiple bonds between the same two atoms (double, triple bonds)
be recorded with their multiplicity. -/
structure Molecule (Atom : Type*) where
  /-- The bonds of the molecule, as unordered pairs of atoms, with multiplicity. -/
  bonds : Multiset (Sym2 Atom)

namespace Molecule

variable {Atom : Type*}

/-- The multiset of bond *ends*: every bond contributes its two ends. -/

theorem handshake_valence_simpleGraph {Atom : Type*} [Fintype Atom]
    (G : SimpleGraph Atom) [DecidableRel G.Adj] :
    ∑ a : Atom, G.degree a = 2 * G.edgeFinset.card :=
  G.sum_degrees_eq_twice_card_edges

end Chem

