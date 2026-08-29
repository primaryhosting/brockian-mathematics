/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not allow a module
-- docstring to precede the `import` commands; the text is otherwise verbatim.)

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

namespace Brockian

open DihedralGroup

/-!
## The dihedral action on the vertices of the `n`-gon

We label the vertices of the regular `n`-gon by `ZMod n`.  With Mathlib's multiplication
convention on `DihedralGroup n` (`r i * sr j = sr (j - i)`), the natural *left* action of the
symmetry group on the vertex set is given by

* `r i • x = x - i`   (rotation),
* `sr i • x = i - x`  (reflection).
-/

/-- The action of a symmetry of the regular `n`-gon on its vertex set `ZMod n`. -/

@[simp] lemma r_smul {n : ℕ} (i x : ZMod n) : (r i : DihedralGroup n) • x = x - i := rfl

