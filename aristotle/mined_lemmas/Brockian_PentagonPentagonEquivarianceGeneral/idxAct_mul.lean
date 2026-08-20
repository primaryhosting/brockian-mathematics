/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
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

/-- The primitive `n`-th root of unity `exp (2 π i / n)`, the basic rotation of a regular
`n`-gon inscribed in the unit circle of `ℂ`. -/

lemma idxAct_mul (g h : DihedralGroup n) (k : ZMod n) :
    idxAct (g * h) k = idxAct g (idxAct h k) := by
  cases g with
  | r i =>
    cases h with
    | r j => simp only [DihedralGroup.r_mul_r, idxAct]; ring
    | sr j => simp only [DihedralGroup.r_mul_sr, idxAct]; ring
  | sr i =>
    cases h with
    | r j => simp only [DihedralGroup.sr_mul_r, idxAct]; ring
    | sr j => simp only [DihedralGroup.sr_mul_sr, idxAct]; ring

omit [NeZero n] in
/-- `geoAct` is a genuine left action of `D n` on the plane. -/
