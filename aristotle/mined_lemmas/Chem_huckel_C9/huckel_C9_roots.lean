import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede all other commands, including module
docstrings, so the required header comment appears immediately after the import.)
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix of the cycle graph `C₉`, with vertices indexed by `ZMod 9`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `9`. -/

theorem huckel_C9_roots :
    C9adj.charpoly.roots =
      (Finset.univ : Finset (ZMod 9)).val.map fun k => 2 * Real.cos (2 * Real.pi * k.val / 9) := by
  rw [huckel_C9]
  rw [Finset.prod_eq_multiset_prod]
  rw [show ((Finset.univ : Finset (ZMod 9)).val.map
        fun k => X - C (2 * Real.cos (2 * Real.pi * k.val / 9)))
      = (((Finset.univ : Finset (ZMod 9)).val.map
        fun k => 2 * Real.cos (2 * Real.pi * k.val / 9)).map fun a => X - C a) by
    rw [Multiset.map_map]; rfl]
  exact Polynomial.roots_multiset_prod_X_sub_C _

end Chem

