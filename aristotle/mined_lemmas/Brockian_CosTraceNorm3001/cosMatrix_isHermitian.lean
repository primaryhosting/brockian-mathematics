/-
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not permit a
-- module docstring before `import`; the module docstring is repeated after the imports.)

import Mathlib

/-!
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The `2 × n` real matrix whose `i`-th column is the unit vector
`(cos (θ i), sin (θ i))`. -/

lemma cosMatrix_isHermitian {n : ℕ} (θ : Fin n → ℝ) : (cosMatrix θ).IsHermitian :=
  (cosMatrix_posSemidef θ).isHermitian

/-- The diagonal entries of the cosine kernel matrix are `cos 0 = 1`, so its trace is `n`. -/
