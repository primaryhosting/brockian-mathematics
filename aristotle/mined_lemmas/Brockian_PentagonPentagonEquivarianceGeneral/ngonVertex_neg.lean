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

lemma ngonVertex_neg (hn : 0 < n) (a : ZMod n) :
    ngonVertex n (-a) = (starRingEnd ℂ) (ngonVertex n a) := by
  have h1 : ngonVertex n (-a) * ngonVertex n a = 1 := by
    rw [← ngonVertex_add hn]
    simp
  rw [← Complex.inv_eq_conj (norm_ngonVertex n a)]
  exact eq_inv_of_mul_eq_one_left h1

