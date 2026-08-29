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

def methane : Molecule (Fin 5) := SimpleGraph.fromRel (fun a b => a = 0 ∨ b = 0)

instance : DecidableRel methane.Adj := fun a b => by
  unfold methane SimpleGraph.fromRel; infer_instance

/-- Carbon is tetravalent in methane. -/
