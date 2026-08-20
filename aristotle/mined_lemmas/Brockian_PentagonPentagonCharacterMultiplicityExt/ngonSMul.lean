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

def ngonSMul {n : ℕ} : DihedralGroup n → ZMod n → ZMod n
  | DihedralGroup.r i, x => x - i
  | DihedralGroup.sr i, x => i - x

/-- The vertex set `ZMod n` of the regular `n`-gon is a `DihedralGroup n`-set. -/
instance ngonMulAction (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  smul := ngonSMul
  one_smul x := by
    show ngonSMul (DihedralGroup.r 0) x = x
    simp [ngonSMul]
  mul_smul := by
    rintro (i | i) (j | j) x <;>
      simp [HSMul.hSMul, SMul.smul, ngonSMul, r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr] <;> ring

