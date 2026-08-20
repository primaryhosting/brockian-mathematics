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

theorem sum_bondIncidence [Fintype V] (e : Sym2 V) : ∑ a : V, bondIncidence a e = 2 := by
  induction e with
  | _ x y => simp [Finset.sum_add_distrib]

/-- **Handshake lemma (chemistry form).** The sum of the atomic valences equals twice the
number of bonds. -/
