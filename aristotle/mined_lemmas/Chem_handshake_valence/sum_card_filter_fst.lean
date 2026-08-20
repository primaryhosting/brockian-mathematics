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
