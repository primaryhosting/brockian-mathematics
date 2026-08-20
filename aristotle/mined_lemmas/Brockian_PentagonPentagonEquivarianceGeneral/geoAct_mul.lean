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

lemma geoAct_mul (g h : DihedralGroup n) (z : ℂ) :
    geoAct (g * h) z = geoAct g (geoAct h z) := by
  cases g with
  | r i =>
    cases h with
    | r j =>
      simp only [DihedralGroup.r_mul_r, geoAct, vertex_add]
      ring
    | sr j =>
      simp only [DihedralGroup.r_mul_sr, geoAct, map_mul, conj_vertex]
      rw [show -(j - i) = i + -j by ring, vertex_add]
      ring
  | sr i =>
    cases h with
    | r j =>
      simp only [DihedralGroup.sr_mul_r, geoAct, vertex_add, mul_assoc]
    | sr j =>
      simp only [DihedralGroup.sr_mul_sr, geoAct, map_mul, conj_vertex,
        Complex.conj_conj]
      rw [neg_neg, show j - i = -i + j by ring, vertex_add]
      ring

/-- The `n` vertices are pairwise distinct, i.e. they really do form a regular `n`-gon. -/
