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
def valence (a : Atom) : ℕ := M.degree a

/-- The number of bonds of a molecule: the number of edges of the bonding graph. -/
noncomputable def bondCount : ℕ := M.edgeFinset.card

/-- **Handshake lemma for valences.**  The sum of the atomic valences in a molecule equals
twice the number of bonds, since every bond contributes one unit of valence to each of the
two atoms it joins.

This is the chemical reading of Mathlib's degree-sum formula
`SimpleGraph.sum_degrees_eq_twice_card_edges`. -/
theorem handshake_valence : ∑ a : Atom, valence M a = 2 * bondCount M :=
  M.sum_degrees_eq_twice_card_edges

/-- Corollary (the classical handshaking lemma in chemical terms): the number of atoms of
odd valence in a molecule is even. -/
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
def multiValence (bonds : Multiset (Atom × Atom)) (a : Atom) : ℕ :=
  (bonds.map fun b => (if b.1 = a then 1 else 0) + (if b.2 = a then 1 else 0)).sum

/-- **Handshake lemma for valences, with bond multiplicities.**  The sum of the atomic
valences equals twice the number of bonds counted with multiplicity. -/
theorem handshake_valence_multi (bonds : Multiset (Atom × Atom)) :
    ∑ a : Atom, multiValence bonds a = 2 * Multiset.card bonds := by
  induction bonds using Multiset.induction with
  | empty => simp [multiValence]
  | cons b s ih =>
      have hb : ∀ a : Atom, multiValence (b ::ₘ s) a
          = ((if b.1 = a then 1 else 0) + (if b.2 = a then 1 else 0)) + multiValence s a := by
        intro a; simp [multiValence]
      have h1 : ∑ a : Atom, (if b.1 = a then 1 else 0) = 1 := by simp
      have h2 : ∑ a : Atom, (if b.2 = a then 1 else 0) = 1 := by simp
      simp only [hb, Finset.sum_add_distrib, ih, h1, h2, Multiset.card_cons]
      omega

end Multi

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

