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
noncomputable def AlkaneSkeleton.bonds (A : AlkaneSkeleton n) : ℕ :=
  A.G.edgeFinset.card

/-- The number of hydrogen atoms: each carbon fills its four valences with hydrogens. -/
noncomputable def AlkaneSkeleton.hydrogens (A : AlkaneSkeleton n) : ℕ :=
  ∑ v, (4 - A.G.degree v)

/-- The carbon skeleton is a tree. -/
theorem AlkaneSkeleton.isTree (A : AlkaneSkeleton n) : A.G.IsTree :=
  ⟨A.connected, A.acyclic⟩

/-- **Alkane tree theorem.**  The carbon skeleton of an acyclic alkane on `n` carbons is a
tree, it has exactly `n - 1` carbon–carbon bonds, and consequently the molecule carries
`2n + 2` hydrogen atoms, i.e. it has formula `CₙH₂ₙ₊₂`. -/
theorem alkane_tree (A : AlkaneSkeleton n) :
    A.G.IsTree ∧ A.bonds + 1 = n ∧ A.hydrogens = 2 * n + 2 := by
  have htree : A.G.IsTree := A.isTree
  -- The edge count of a tree: `SimpleGraph.IsTree.card_edgeFinset`.
  have hb : A.bonds + 1 = n := by
    have := htree.card_edgeFinset
    simpa [AlkaneSkeleton.bonds] using this
  refine ⟨htree, hb, ?_⟩
  -- Degree-sum formula: `SimpleGraph.sum_degrees_eq_twice_card_edges`.
  have hdeg : ∑ v, A.G.degree v = 2 * A.bonds := by
    simpa [AlkaneSkeleton.bonds] using A.G.sum_degrees_eq_twice_card_edges
  have hsum : A.hydrogens + ∑ v, A.G.degree v = 4 * n := by
    rw [AlkaneSkeleton.hydrogens, ← Finset.sum_add_distrib]
    have : ∀ v : Fin n, (4 - A.G.degree v) + A.G.degree v = 4 := fun v =>
      Nat.sub_add_cancel (A.valence v)
    simp [this, mul_comm]
  rw [hdeg] at hsum
  omega

/-- Methane, `CH₄`: the one-carbon skeleton.  This witnesses that the hypotheses of
`Chem.alkane_tree` are satisfiable. -/
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

