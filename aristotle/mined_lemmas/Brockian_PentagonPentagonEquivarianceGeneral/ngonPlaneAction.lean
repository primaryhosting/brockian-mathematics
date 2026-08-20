/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian

/-- The `k`-th vertex of the regular `n`-gon inscribed in the unit circle of `ℂ`,
indexed by `k : ZMod n`. -/

noncomputable def ngonPlaneAction (n : ℕ) : DihedralGroup n → ℂ → ℂ
  | .r i, z => ngonVertex n (-i) * z
  | .sr i, z => ngonVertex n i * (starRingEnd ℂ) z

section Lemmas

variable {n : ℕ}

/-- Two natural numbers congruent mod `n` give the same `n`-th root of unity. -/
