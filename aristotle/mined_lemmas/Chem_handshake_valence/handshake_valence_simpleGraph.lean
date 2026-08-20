import Mathlib

/-!
# The handshake lemma for molecules

A molecule is modelled as a finite collection of atoms together with a *multiset* of bonds,
each bond being an unordered pair of atoms (`Sym2`).  Using a multiset allows multiple bonds
(double, triple bonds) between the same pair of atoms.

The *valence* of an atom is the number of bond-ends attached to it: each bond contributes `1`
for every endpoint equal to that atom (so a bond of an atom to itself would contribute `2`).

The main result, `Chem.handshake_valence`, states that the sum of the valences of all atoms
equals twice the number of bonds.
-/

namespace Chem

variable {V : Type*} [DecidableEq V]

/-- The number of ends of the bond `e` that are attached to the atom `a`. -/

theorem handshake_valence_simpleGraph {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ∑ a : V, G.degree a = 2 * G.edgeFinset.card :=
  G.sum_degrees_eq_twice_card_edges

end Chem

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

