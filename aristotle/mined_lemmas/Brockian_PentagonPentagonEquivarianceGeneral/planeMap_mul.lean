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

/-!
# The dihedral symmetries of a regular `n`-gon, and their equivariance

This file generalizes the `D₅` (pentagon) representation results to arbitrary regular `n`-gons.

The vertices of the regular `n`-gon are the `n`-th roots of unity
`ngonVertex n k = exp (2 π i k / n)`, indexed by `k : ZMod n`.

`DihedralGroup n` acts
* combinatorially on the index set `ZMod n` (`Brockian.vertexAction`), and
* geometrically on the complex plane by rotations and reflections (`Brockian.planeMap`).

The main theorem `Brockian.PentagonPentagonEquivarianceGeneral` states that the vertex map
`ZMod n → ℂ` intertwines these two actions, for every `n ≠ 0`.  The pentagon case `n = 5`
is recovered as `Brockian.pentagon_equivariance`.
-/

namespace Brockian

open Complex

/-! ### Vertices of the regular `n`-gon -/

/-- The `k`-th vertex of the regular `n`-gon inscribed in the unit circle:
`exp (2 π i k / n)`. -/

lemma planeMap_mul (g h : DihedralGroup n) (z : ℂ) :
    planeMap (g * h) z = planeMap g (planeMap h z) := by
  cases g with
  | r i =>
      cases h with
      | r j =>
          simp only [DihedralGroup.r_mul_r, planeMap_r]
          rw [ngonVertex_add, mul_assoc]
      | sr j =>
          simp only [DihedralGroup.r_mul_sr, planeMap_sr, planeMap_r]
          rw [← mul_assoc, ← ngonVertex_add]
          ring_nf
  | sr i =>
      cases h with
      | r j =>
          simp only [DihedralGroup.sr_mul_r, planeMap_sr, planeMap_r, map_mul]
          rw [← mul_assoc, ← ngonVertex_neg, ← ngonVertex_add]
          ring_nf
      | sr j =>
          simp only [DihedralGroup.sr_mul_sr, planeMap_sr, planeMap_r, map_mul,
            RingHomCompTriple.comp_apply, RingHom.id_apply]
          rw [← ngonVertex_neg, neg_neg, ← mul_assoc, ← ngonVertex_add]
          ring_nf

/-- The geometric action of the dihedral group on the plane. -/
noncomputable instance : MulAction (DihedralGroup n) ℂ where
  smul := planeMap
  one_smul := planeMap_one
  mul_smul := planeMap_mul

