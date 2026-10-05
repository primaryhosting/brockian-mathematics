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

import Mathlib
/-!
# Alkane Tree
Category: Chemistry
Target: Chem.alkane_tree
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset SimpleGraph

/--
**The carbon skeleton of an acyclic alkane is a tree with `n - 1` C–C bonds.**

Model: `V` is the (finite, nonempty) set of carbon atoms of a molecule, `G` is its
carbon skeleton (`G.Adj u v` means there is a C–C single bond between `u` and `v`),
and `hyd v` is the number of hydrogen atoms bonded to carbon `v`.

Chemical hypotheses:
* the molecule is a single connected acyclic species (`hconn`, `hacyc`);
* every carbon is tetravalent: its C–C bonds together with its C–H bonds number `4`
  (`hval`).

Conclusions: the skeleton is a tree, it has exactly `n - 1` C–C bonds where
`n = #carbons`, and the molecular formula is `CₙH₂ₙ₊₂`.
-/
theorem alkane_tree {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hyd : V → ℕ) (n : ℕ) (hn : Fintype.card V = n)
    (hconn : G.Connected) (hacyc : G.IsAcyclic)
    (hval : ∀ v, G.degree v + hyd v = 4) :
    G.IsTree ∧ G.edgeFinset.card = n - 1 ∧ ∑ v, hyd v = 2 * n + 2 := by
  have htree : G.IsTree := (G.isTree_iff).2 ⟨hconn, hacyc⟩
  have hE : G.edgeFinset.card + 1 = n := by
    rw [← hn]; exact htree.card_edgeFinset
  -- Valence bookkeeping: summing `deg v + hyd v = 4` over all carbons.
  have hsum : ∑ v, (G.degree v + hyd v) = 4 * n := by
    rw [Finset.sum_congr rfl (fun v _ => hval v)]
    simp [← hn, mul_comm]
  rw [Finset.sum_add_distrib, G.sum_degrees_eq_twice_card_edges] at hsum
  refine ⟨htree, by omega, by omega⟩

/-- Non-vacuity check: methane `CH₄` (one carbon, no C–C bonds, four hydrogens)
satisfies the hypotheses, and the theorem yields `0` C–C bonds and `4` hydrogens. -/
example : (⊥ : SimpleGraph Unit).IsTree ∧ (⊥ : SimpleGraph Unit).edgeFinset.card = 1 - 1 ∧
    ∑ _v : Unit, 4 = 2 * 1 + 2 :=
  by
    simpa using alkane_tree (⊥ : SimpleGraph Unit) (fun _ => 4) 1 (by simp)
      Connected.of_subsingleton isAcyclic_bot (by simp)

end Chem

