import Mathlib

/-!
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
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

namespace Brockian

open MulAction DihedralGroup

/-! ## The action of the dihedral group on the vertices of the regular `n`-gon -/

/-- The symmetry action of `DihedralGroup n` on the vertex set `ZMod n` of the regular `n`-gon:
the rotation `r i` sends a vertex `x` to `x - i`, and the reflection `sr i` sends `x` to `i - x`. -/

theorem ngon_orbits_card (n : ℕ) [NeZero n]
    [Fintype (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n)))] :
    Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n))) = 1 := by
  have hs : Subsingleton (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n))) := by
    constructor
    rintro ⟨a⟩ ⟨b⟩
    refine Quotient.sound ?_
    show (MulAction.orbitRel (DihedralGroup n) (ZMod n)) a b
    rw [MulAction.orbitRel_apply]
    exact (MulAction.mem_orbit_iff).mpr (MulAction.exists_smul_eq (DihedralGroup n) b a)
  exact Fintype.card_eq_one_iff_nonempty_unique.mpr
    ⟨@uniqueOfSubsingleton _ hs (Quotient.mk _ 0)⟩

/-- Burnside's lemma for the vertex action: the total number of fixed points equals the order of
the dihedral group, since the action is transitive. -/
