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

def bondIncidence (a : V) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun x y => (if x = a then 1 else 0) + (if y = a then 1 else 0),
    fun x y => by ring⟩

@[simp]
