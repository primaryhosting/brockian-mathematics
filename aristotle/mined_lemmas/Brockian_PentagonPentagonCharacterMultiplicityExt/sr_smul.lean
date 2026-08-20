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

@[simp] theorem sr_smul {n : ℕ} (i x : ZMod n) : (DihedralGroup.sr i) • x = i - x := rfl

/-- The dihedral group acts transitively on the vertices of the regular `n`-gon. -/
instance ngonPretransitive (n : ℕ) : MulAction.IsPretransitive (DihedralGroup n) (ZMod n) :=
  ⟨fun x y => ⟨DihedralGroup.r (x - y), by simp⟩⟩

/-! ## The permutation character -/

/-- The permutation character of the vertex representation of `DihedralGroup n`: the value at `g`
is the number of vertices fixed by `g`. -/
