import Mathlib

/-!
# Handshake Valence
Category: Chemistry
Target: Chem.handshake_valence
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- A molecule (with single bonds only, and no self-bonds) modelled as a simple graph
whose vertices are the atoms and whose edges are the chemical bonds. -/
abbrev Molecule (Atom : Type*) := SimpleGraph Atom

variable {Atom : Type*} [Fintype Atom] (M : Molecule Atom) [DecidableRel M.Adj]

/-- The valence of an atom in a molecule: the number of bonds incident to it. -/
def valence (a : Atom) : ℕ := M.degree a

/-- The number of bonds in a molecule. -/
def numBonds : ℕ := M.edgeFinset.card

/-- **Handshake lemma for valences.** The sum of the atomic valences (vertex degrees)
in a molecule equals twice the number of bonds (edges).

This is Mathlib's `SimpleGraph.sum_degrees_eq_twice_card_edges`. -/
theorem handshake_valence :
    ∑ a : Atom, valence M a = 2 * numBonds M :=
  M.sum_degrees_eq_twice_card_edges

/-! ### Sanity check: methane, CH₄ -/

/-- Methane, CH₄: atom `0` is the carbon, atoms `1, 2, 3, 4` are the hydrogens,
and every hydrogen is bonded to the carbon. -/
def methane : Molecule (Fin 5) := SimpleGraph.fromRel (fun a b => a = 0 ∨ b = 0)

instance : DecidableRel methane.Adj := fun a b => by
  unfold methane SimpleGraph.fromRel; infer_instance

/-- Carbon is tetravalent in methane. -/
lemma valence_methane_carbon : valence methane 0 = 4 := by decide

/-- Each hydrogen in methane is monovalent. -/
lemma valence_methane_hydrogen (a : Fin 5) (ha : a ≠ 0) : valence methane a = 1 := by
  fin_cases a <;> simp_all <;> decide

/-- Methane has four bonds. -/
lemma numBonds_methane : numBonds methane = 4 := by decide

/-- The handshake identity for methane: `4 + 1 + 1 + 1 + 1 = 2 * 4`. -/
example : ∑ a : Fin 5, valence methane a = 2 * numBonds methane :=
  handshake_valence methane

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

