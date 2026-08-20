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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

open Complex DihedralGroup

/-! ## Vertices of the regular `n`-gon

The vertices of the regular `n`-gon inscribed in the unit circle of `ℂ` are indexed by
`ZMod n`; the vertex with index `k` is `exp (2 * π * I * k / n)`.  We use Mathlib's additive
character `ZMod.toCircle : AddChar (ZMod N) Circle`, so that the "rotation" identity
`vertex (a + b) = vertex a * vertex b` is inherited from `AddChar.map_add_eq_mul`. -/

/-- The `k`-th vertex of the regular `n`-gon inscribed in the unit circle of `ℂ`,
namely `exp (2 * π * I * k / n)`. -/

lemma dihedralRep_mul (g h : DihedralGroup n) (z : ℂ) :
    dihedralRep (g * h) z = dihedralRep g (dihedralRep h z) := by
  cases g with
  | r i =>
    cases h with
    | r j =>
      simp only [r_mul_r, dihedralRep_r, vertex_add]
      ring
    | sr j =>
      simp only [r_mul_sr, dihedralRep_sr, dihedralRep_r, map_mul]
      rw [sub_eq_add_neg, vertex_add, vertex_neg, map_mul, Complex.conj_conj]
      ring
  | sr i =>
    cases h with
    | r j =>
      simp only [sr_mul_r, dihedralRep_sr, dihedralRep_r, map_mul, vertex_add]
      ring
    | sr j =>
      simp only [sr_mul_sr, dihedralRep_sr, dihedralRep_r, map_mul,
        Complex.conj_conj]
      rw [sub_eq_add_neg, vertex_add, vertex_neg]
      ring

/-- Every element of the dihedral group acts on the plane by an isometry (indeed by a
norm-preserving map). -/
