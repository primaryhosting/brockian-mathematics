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

