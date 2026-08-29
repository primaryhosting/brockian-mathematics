import Mathlib

/-!
# Alkane Tree
Category: Chemistry
Target: Chem.alkane_tree
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

namespace Chem

/-- The carbon skeleton of an acyclic alkane with `n` carbon atoms: a simple graph on the
`n` carbons which is connected (the molecule is one piece), acyclic (the alkane is acyclic,
i.e. not a cycloalkane) and in which every carbon has at most `4` bonds (carbon is
tetravalent). -/
structure AlkaneSkeleton (n : ℕ) where
  /-- The graph of carbon–carbon bonds. -/
  G : SimpleGraph (Fin n)
  /-- The skeleton is connected. -/
  connected : G.Connected
  /-- The skeleton is acyclic. -/
  acyclic : G.IsAcyclic
  /-- Carbon is tetravalent: at most four bonds at each carbon. -/
  valence : ∀ v, G.degree v ≤ 4

variable {n : ℕ}

/-- The number of C–C bonds in the skeleton. -/

def methane : AlkaneSkeleton 1 where
  G := ⊥
  connected := (SimpleGraph.IsTree.of_subsingleton (G := (⊥ : SimpleGraph (Fin 1)))).isConnected
  acyclic := SimpleGraph.isAcyclic_bot
  valence v := by simp

example : methane.bonds + 1 = 1 ∧ methane.hydrogens = 4 :=
  ⟨(alkane_tree methane).2.1, (alkane_tree methane).2.2⟩

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

