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

lemma ngonVertex_add (hn : 0 < n) (a b : ZMod n) :
    ngonVertex n (a + b) = ngonVertex n a * ngonVertex n b := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hcast : (((a + b).val : ℕ) : ZMod n) = ((a.val + b.val : ℕ) : ZMod n) := by
    push_cast [ZMod.natCast_zmod_val]
    ring
  have h1 : ngonVertex n (a + b)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a.val + b.val : ℕ) : ℂ) / (n : ℂ)) :=
    exp_nat_congr hn hcast
  rw [h1]
  unfold ngonVertex
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

