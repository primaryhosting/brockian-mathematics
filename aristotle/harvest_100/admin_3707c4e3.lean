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
def ends (M : Molecule Atom) : Multiset Atom :=
  M.bonds.bind Sym2.toMultiset

/-- The valence of an atom: the number of bond ends attached to it (a double
bond contributes `2`). -/
def valence [DecidableEq Atom] (M : Molecule Atom) (a : Atom) : ℕ :=
  M.ends.count a

/-- The number of bonds of the molecule. -/
def bondCount (M : Molecule Atom) : ℕ :=
  Multiset.card M.bonds

/-- Every bond has exactly two ends, so the total number of bond ends is twice
the number of bonds. -/
theorem card_ends (M : Molecule Atom) :
    Multiset.card M.ends = 2 * M.bondCount := by
  simp [ends, bondCount, Multiset.card_bind, Sym2.card_toMultiset, Multiset.map_const',
    Multiset.sum_replicate, mul_comm]

end Molecule

/-- **Handshake lemma for valences.**  The sum of the valences (numbers of bond
ends) of all atoms of a molecule equals twice the number of bonds. -/
theorem handshake_valence {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    (M : Molecule Atom) :
    ∑ a : Atom, M.valence a = 2 * M.bondCount := by
  have h : ∑ a ∈ M.ends.toFinset, M.ends.count a = Multiset.card M.ends :=
    Multiset.toFinset_sum_count_eq M.ends
  have h2 : ∑ a : Atom, M.valence a = ∑ a ∈ M.ends.toFinset, M.ends.count a := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro a _ ha
    simpa [Molecule.valence, Multiset.count_eq_zero] using
      (Multiset.mem_toFinset.not.mp ha)
  rw [h2, h, M.card_ends]

/-- The classical graph-theoretic form: for a molecular structure given by a
simple graph (only single bonds), the sum of the vertex degrees equals twice
the number of edges. -/
theorem handshake_valence_simpleGraph {Atom : Type*} [Fintype Atom]
    (G : SimpleGraph Atom) [DecidableRel G.Adj] :
    ∑ a : Atom, G.degree a = 2 * G.edgeFinset.card :=
  G.sum_degrees_eq_twice_card_edges

end Chem

