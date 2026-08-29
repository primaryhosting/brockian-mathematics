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

lemma valence_methane_hydrogen (a : Fin 5) (ha : a ≠ 0) : valence methane a = 1 := by
  fin_cases a <;> simp_all <;> decide

/-- Methane has four bonds. -/
