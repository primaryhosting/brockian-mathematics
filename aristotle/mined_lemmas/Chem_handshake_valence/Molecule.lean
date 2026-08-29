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
