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
Category: Chemistry
Target: Chem.handshake_valence
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A molecule (a multigraph on the atom set `V`): a multiset of bonds, each bond
recorded as a pair of atoms.  Using a multiset allows multiple bonds (double,
triple bonds) between the same pair of atoms. -/
abbrev Bonds (V : Type*) := Multiset (V × V)

/-- The valence of an atom `a`: the number of bond-endpoints attached to `a`.
A bond joining `a` to another atom contributes `1`; a bond from `a` to itself
contributes `2`. -/
def valence (bonds : Bonds V) (a : V) : ℕ :=
  Multiset.card (bonds.filter fun b => b.1 = a) +
  Multiset.card (bonds.filter fun b => b.2 = a)

/-- Counting the first endpoints of all bonds recovers the number of bonds. -/
lemma sum_card_filter_fst (bonds : Bonds V) :
    ∑ a : V, Multiset.card (bonds.filter fun b => b.1 = a) = Multiset.card bonds := by
  induction bonds using Multiset.induction with
  | empty => simp
  | cons b s ih =>
      simp only [Multiset.filter_cons, Multiset.card_add, Finset.sum_add_distrib, ih,
        Multiset.card_cons]
      have : ∑ a : V, Multiset.card (if b.1 = a then {b} else (0 : Multiset (V × V))) = 1 := by
        rw [Finset.sum_eq_single b.1]
        · simp
        · intro a _ ha
          simp [Ne.symm ha]
        · intro h
          exact absurd (Finset.mem_univ b.1) h
      omega

/-- Counting the second endpoints of all bonds recovers the number of bonds. -/
lemma sum_card_filter_snd (bonds : Bonds V) :
    ∑ a : V, Multiset.card (bonds.filter fun b => b.2 = a) = Multiset.card bonds := by
  induction bonds using Multiset.induction with
  | empty => simp
  | cons b s ih =>
      simp only [Multiset.filter_cons, Multiset.card_add, Finset.sum_add_distrib, ih,
        Multiset.card_cons]
      have : ∑ a : V, Multiset.card (if b.2 = a then {b} else (0 : Multiset (V × V))) = 1 := by
        rw [Finset.sum_eq_single b.2]
        · simp
        · intro a _ ha
          simp [Ne.symm ha]
        · intro h
          exact absurd (Finset.mem_univ b.2) h
      omega

/-- **Handshake lemma (chemical valence form).**  The sum of the valences of all
atoms in a molecule equals twice the number of bonds. -/
theorem handshake_valence (bonds : Bonds V) :
    ∑ a : V, valence bonds a = 2 * Multiset.card bonds := by
  unfold valence
  rw [Finset.sum_add_distrib, sum_card_filter_fst, sum_card_filter_snd]
  ring

omit [DecidableEq V] in
/-- The same statement for a `SimpleGraph`: the sum of the degrees of the vertices
is twice the number of edges. -/
theorem handshake_valence_simpleGraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ a : V, G.degree a = 2 * G.edgeFinset.card :=
  G.sum_degrees_eq_twice_card_edges

end Chem

#print axioms Chem.handshake_valence
#print axioms Chem.handshake_valence_simpleGraph

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

