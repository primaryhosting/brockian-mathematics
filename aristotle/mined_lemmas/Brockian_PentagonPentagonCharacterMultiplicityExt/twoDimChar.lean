/-
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian

open DihedralGroup

/-! ## The action of the dihedral group on the vertices of the `n`-gon -/

/-- The action of `DihedralGroup n` on the `n` vertices of the regular `n`-gon,
whose vertices are labelled by `ZMod n`.  The rotation `r i` sends the vertex `x` to
`x - i` and the reflection `sr i` sends `x` to `i - x`. -/

noncomputable def twoDimChar (n h : ℕ) : DihedralGroup n → ℂ
  | .r i => dihedralZeta n ^ (h * i.val) + (dihedralZeta n)⁻¹ ^ (h * i.val)
  | .sr _ => 0

