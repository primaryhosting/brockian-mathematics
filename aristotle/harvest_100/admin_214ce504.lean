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

/-! ## The handshake lemma for molecules

A molecule is modelled as a (multi)graph: atoms are the vertices and bonds are the edges.
The *valence* of an atom is the number of bonds incident to it (its vertex degree), where a
double bond counts twice, a triple bond three times, and so on.  The handshake lemma says that
the total valence of a molecule is twice its number of bonds.
-/

/-- A molecule: a finite set of `Atom`s together with a finite set of `Bond`s, each bond joining
two *distinct* atoms.  Several bonds may join the same pair of atoms, which models double and
triple bonds. -/
structure Molecule (Atom : Type*) [Fintype Atom] [DecidableEq Atom] where
  /-- The type of bonds of the molecule. -/
  Bond : Type*
  [bondFintype : Fintype Bond]
  /-- The (unordered) pair of atoms joined by a bond. -/
  ends : Bond → Sym2 Atom
  /-- No atom is bonded to itself. -/
  ends_not_isDiag : ∀ b : Bond, ¬ (ends b).IsDiag

attribute [instance] Molecule.bondFintype

variable {Atom : Type*} [Fintype Atom] [DecidableEq Atom]

/-- The valence of an atom: the number of bonds incident to it, counted with multiplicity
(so a double bond contributes `2`). -/
noncomputable def Molecule.valence (M : Molecule Atom) (a : Atom) : ℕ :=
  (Finset.univ.filter fun b : M.Bond => a ∈ M.ends b).card

/-- The number of bonds of a molecule, counted with multiplicity. -/
noncomputable def Molecule.numBonds (M : Molecule Atom) : ℕ := Fintype.card M.Bond

/-- Each bond has exactly two distinct endpoints. -/
theorem Molecule.card_ends (M : Molecule Atom) (b : M.Bond) :
    (Finset.univ.filter fun a : Atom => a ∈ M.ends b).card = 2 := by
  have : (Finset.univ.filter fun a : Atom => a ∈ M.ends b) = (M.ends b).toFinset := by
    ext a
    simp [Sym2.mem_toFinset]
  rw [this, Sym2.card_toFinset_of_not_isDiag _ (M.ends_not_isDiag b)]

/-- **Handshake lemma (chemistry form).**  The sum of the atomic valences of a molecule equals
twice its number of bonds. -/
theorem handshake_valence (M : Molecule Atom) :
    ∑ a : Atom, M.valence a = 2 * M.numBonds := by
  classical
  have h : ∀ a : Atom, M.valence a
      = ∑ b : M.Bond, if a ∈ M.ends b then 1 else 0 := by
    intro a
    rw [Molecule.valence, Finset.card_filter]
  simp only [h]
  rw [Finset.sum_comm]
  have h2 : ∀ b : M.Bond, (∑ a : Atom, if a ∈ M.ends b then 1 else 0) = 2 := by
    intro b
    rw [← Finset.card_filter]
    exact M.card_ends b
  simp only [h2, Finset.sum_const, smul_eq_mul]
  rw [Molecule.numBonds, ← Finset.card_univ, mul_comm]

omit [DecidableEq Atom] in
/-- The handshake lemma for a simple molecular graph: the sum of the atomic valences (vertex
degrees) equals twice the number of bonds (edges). -/
theorem handshake_valence_simpleGraph (G : SimpleGraph Atom) [DecidableRel G.Adj] :
    ∑ a : Atom, G.degree a = 2 * G.edgeFinset.card :=
  G.sum_degrees_eq_twice_card_edges

end Chem

