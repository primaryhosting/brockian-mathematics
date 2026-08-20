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
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

/-- A molecule: a finite collection of atoms together with a bonding relation.
Two distinct atoms are either bonded or not (single bonds only), and bonding is
symmetric. This is exactly the data of a simple graph on the atom set. -/
structure Molecule where
  /-- The type of atoms of the molecule. -/
  Atom : Type
  [atomFintype : Fintype Atom]
  [atomDecEq : DecidableEq Atom]
  /-- The bonding relation between atoms. -/
  bonds : SimpleGraph Atom
  [bondsDec : DecidableRel bonds.Adj]

attribute [instance] Molecule.atomFintype Molecule.atomDecEq Molecule.bondsDec

/-- The valence of an atom in a molecule: the number of atoms bonded to it. -/
def Molecule.valence (M : Molecule) (a : M.Atom) : ℕ :=
  M.bonds.degree a

/-- The number of bonds in a molecule. -/
def Molecule.bondCount (M : Molecule) : ℕ :=
  M.bonds.edgeFinset.card

/-- **Handshake valence rule.** In any molecule, the sum of the valences of the
atoms equals twice the number of bonds. -/
theorem handshake_valence (M : Molecule) :
    ∑ a : M.Atom, M.valence a = 2 * M.bondCount := by
  simpa [Molecule.valence, Molecule.bondCount] using
    M.bonds.sum_degrees_eq_twice_card_edges

end Chem

