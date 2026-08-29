/-
# Handshake Valence
Category: Chemistry
Target: Chem.handshake_valence
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Handshake Valence

The handshake (degree-sum) lemma in chemical language: for any molecule, the sum of the
valences of its atoms equals twice the number of its bonds, where a bond of order `k`
(double, triple, ...) is counted `k` times.
-/

namespace Chem

open Finset

/-- A molecular structure on a type of atoms `V`: a multiset of bonds, each bond being an
unordered pair of atoms.  Multiple bonds (double, triple, ...) are recorded as repeated
entries of the same pair, so `bonds` is a multiset rather than a set. -/
structure Molecule (V : Type*) where
  /-- The bonds of the molecule, as a multiset of unordered pairs of atoms. -/
  bonds : Multiset (Sym2 V)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The valence (degree) of an atom: the number of bond endpoints attached to it, so that a
bond of order `k` contributes `k` to each of its two atoms. -/
def Molecule.valence (M : Molecule V) (a : V) : ℕ :=
  (M.bonds.map fun e => Multiset.count a e.toMultiset).sum

/-- Summing the multiplicities of all atoms in a multiset of atoms gives its cardinality. -/
theorem sum_count_univ (s : Multiset V) :
    ∑ a : V, Multiset.count a s = Multiset.card s := by
  rw [← Multiset.toFinset_sum_count_eq s]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro a _ ha
  simpa using ha

/-- **Handshake lemma for valences.**  The sum of the valences of all atoms of a molecule
equals twice the number of its bonds (a double bond counting as two bonds, etc.). -/
theorem handshake_valence (M : Molecule V) :
    ∑ a : V, M.valence a = 2 * Multiset.card M.bonds := by
  obtain ⟨bonds⟩ := M
  simp only [Molecule.valence]
  induction bonds using Multiset.induction_on with
  | empty => simp
  | cons e t ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Finset.sum_add_distrib, ih,
        Multiset.card_cons]
      rw [sum_count_univ, Sym2.card_toMultiset]
      ring

/-! ### Specialization to simple molecular graphs -/

omit [Fintype V] in
/-- In a bond without a self-loop, an atom occurs at most once as an endpoint. -/
theorem count_toMultiset_of_not_isDiag (e : Sym2 V) (he : ¬ e.IsDiag) (a : V) :
    Multiset.count a e.toMultiset = if a ∈ e then 1 else 0 := by
  induction e with
  | _ x y =>
    simp only [Sym2.isDiag_iff_proj_eq] at he
    simp only [Sym2.toMultiset, Sym2.mem_iff]
    rcases eq_or_ne a x with rfl | hax
    · simp [he]
    · rcases eq_or_ne a y with rfl | hay
      · simp [hax, Ne.symm hax]
      · simp [hax, hay]

/-- The molecule associated with a simple graph of single bonds. -/
def Molecule.ofSimpleGraph (G : SimpleGraph V) [DecidableRel G.Adj] : Molecule V :=
  ⟨G.edgeFinset.val⟩

/-- For a molecule with only single bonds, the valence of an atom is its graph degree. -/
theorem Molecule.valence_ofSimpleGraph (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) :
    (Molecule.ofSimpleGraph G).valence a = G.degree a := by
  have hsum : (Molecule.ofSimpleGraph G).valence a
      = ∑ e ∈ G.edgeFinset, Multiset.count a e.toMultiset := rfl
  rw [hsum, Finset.sum_congr rfl fun e he =>
    count_toMultiset_of_not_isDiag e
      (G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 he)) a,
    ← Finset.card_filter]
  have h : G.edgeFinset.filter (fun e => a ∈ e) = G.incidenceFinset a := by
    ext e
    simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, and_comm]
  rw [h, G.card_incidenceFinset_eq_degree]

/-- The handshake lemma for a simple molecular graph: the sum of the atoms' valences is
twice the number of bonds. -/
theorem handshake_valence_simpleGraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ a : V, G.degree a = 2 * #G.edgeFinset := by
  have h := handshake_valence (Molecule.ofSimpleGraph G)
  rw [Finset.sum_congr rfl fun a _ => (Molecule.valence_ofSimpleGraph G a).symm]
  simpa [Molecule.ofSimpleGraph] using h

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

