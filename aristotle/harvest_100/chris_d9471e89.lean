/-
# Alkane Tree
Category: Chemistry
Target: Chem.alkane_tree
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Alkane Tree
Category: Chemistry
Target: Chem.alkane_tree
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

/-- **Alkane skeleton.**  A model of an acyclic (saturated, connected) hydrocarbon:
`V` is the set of carbon atoms, `G` records the C–C bonds, `H v` is the number of
hydrogen atoms attached to the carbon `v`, and every carbon is tetravalent, i.e. its
C–C bonds together with its C–H bonds number exactly four. -/
structure AlkaneSkeleton (V : Type*) [Fintype V] where
  /-- the graph of carbon–carbon bonds -/
  bonds : SimpleGraph V
  /-- decidability of adjacency, for counting -/
  decAdj : DecidableRel bonds.Adj
  /-- the molecule is connected -/
  connected : bonds.Connected
  /-- the carbon skeleton contains no ring -/
  acyclic : bonds.IsAcyclic
  /-- number of hydrogens bonded to each carbon -/
  hydrogens : V → ℕ
  /-- carbon is tetravalent -/
  tetravalent : ∀ v, bonds.degree v + hydrogens v = 4

attribute [instance] AlkaneSkeleton.decAdj

/-- **The carbon skeleton of an acyclic alkane is a tree.** -/
theorem AlkaneSkeleton.isTree {V : Type*} [Fintype V] (A : AlkaneSkeleton V) :
    A.bonds.IsTree :=
  ⟨A.connected, A.acyclic⟩

/-- **Alkane tree theorem.**  For an acyclic alkane with `n` carbon atoms, the carbon
skeleton is a tree (connected and acyclic) with exactly `n - 1` carbon–carbon bonds,
and the molecular formula is `CₙH₂ₙ₊₂`: the total number of hydrogen atoms is `2n + 2`. -/
theorem alkane_tree {V : Type*} [Fintype V] (A : AlkaneSkeleton V)
    (n : ℕ) (hn : Fintype.card V = n) :
    A.bonds.IsTree ∧ A.bonds.edgeFinset.card + 1 = n ∧ ∑ v, A.hydrogens v = 2 * n + 2 := by
  classical
  have htree : A.bonds.IsTree := A.isTree
  have hedge : A.bonds.edgeFinset.card + 1 = n := by
    have h := htree.card_edgeFinset
    omega
  refine ⟨htree, hedge, ?_⟩
  have hsum : ∑ v, (A.bonds.degree v + A.hydrogens v) = 4 * Fintype.card V := by
    simp [A.tetravalent, Finset.sum_const, mul_comm]
  rw [Finset.sum_add_distrib, A.bonds.sum_degrees_eq_twice_card_edges] at hsum
  omega
#print axioms Chem.alkane_tree

end Chem

