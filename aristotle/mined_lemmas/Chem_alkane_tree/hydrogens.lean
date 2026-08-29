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

/-
# Alkane Tree
Category: Chemistry
Target: Chem.alkane_tree
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset

/-- The number of hydrogen atoms attached to the carbon atom `v` of a carbon
skeleton `G`: carbon is tetravalent, so the valences left over after the C–C
bonds at `v` are saturated by hydrogens. -/

def hydrogens {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) : ℕ :=
  4 - G.degree v

/-- **The carbon skeleton of an acyclic alkane.**

If the carbon skeleton `G` of a molecule with `n` carbon atoms is connected and
acyclic (i.e. a tree), and carbon is tetravalent (each atom has at most `4` bonds),
then the skeleton has exactly `n - 1` C–C bonds, and the molecule carries exactly
`2n + 2` hydrogen atoms, i.e. it has formula `CₙH₂ₙ₊₂`. -/
